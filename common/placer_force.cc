

#include "placer_force.h"
#include <algorithm>
#include <chrono>
#include <map>
#include <queue>
#include <string>
#include <vector>
#include "place_common.h"
#include "placer1.h"
#include "timing.h"
#include "util.h"

namespace std {
template <> struct hash<std::pair<NEXTPNR_NAMESPACE_PREFIX IdString, std::size_t>>
{
    std::size_t operator()(const std::pair<NEXTPNR_NAMESPACE_PREFIX IdString, std::size_t> &idp) const noexcept
    {
        std::size_t seed = 0;
        boost::hash_combine(seed, hash<NEXTPNR_NAMESPACE_PREFIX IdString>()(idp.first));
        boost::hash_combine(seed, hash<std::size_t>()(idp.second));
        return seed;
    }
};
} // namespace std

NEXTPNR_NAMESPACE_BEGIN

class ForcePlacer
{
  private:
    struct BoundingBox
    {
        // Actural bounding box
        int x0 = 0, x1 = 0, y0 = 0, y1 = 0;
        // Number of Cells at bounding edge
        int nx0 = 0, nx1 = 0, ny0 = 0, ny1 = 0;
        wirelen_t hpwl(const PlacerFCfg &cfg) const
        {
            return wirelen_t(cfg.hpwl_scale_x * abs(x1 - x0) + cfg.hpwl_scale_y * abs(y1 - y0));
        }
    };

    // 在布局算法初期允许cell自由移动
    struct CellLocation
    {
        int x, y;             // 当前位置
        int legal_x, legal_y; // 合法化位置
        double rawx, rawy;    // 力算法得到的原始位置
        bool locked = false, global = false;

        CellLocation() {}
        CellLocation(Loc loc)
        {
            x = loc.x;
            y = loc.y;
            rawx = double(x);
            rawy = double(y);
        }
        void legal()
        {
            legal_x = x;
            legal_y = y;
        }
    };

    // Star算法中间变量
    struct NetStar
    {
        double xc, yc;                     // 线网的平均中心，xc = sum(x_i) / len(net) ，其中x_i为所有相连port的位置
        double x_divergence, y_divergence; // Divergence = \sqrt{sum((x_i - xc)^2) + 1} ，参考star+算法的S变量
        int net_len;                       // net中链接的Cell数量
    };

  public:
    ForcePlacer(Context *ctx, PlacerFCfg cfg) : ctx(ctx), cfg(cfg)
    {
        // 统计每种bel的数量和bel的种类
        int num_bel_types = 0;
        for (auto bel : ctx->getBels()) {
            IdString type = ctx->getBelType(bel);
            if (bel_types.find(type) == bel_types.end()) {
                bel_types[type] = std::tuple<int, int>(num_bel_types++, 1);
            } else {
                std::get<1>(bel_types.at(type))++;
            }
        }
        // 统计每类bel的位置，getbel得到一个bel的id，需要利用arch提供的getlocation和gettype得知id对应的BEL位置和类型
        for (auto bel : ctx->getBels()) {
            Loc loc = ctx->getBelLocation(bel);
            IdString type = ctx->getBelType(bel);
            int type_idx = std::get<0>(bel_types[type]);
            int type_cnt = std::get<1>(bel_types[type]);
            if (type_cnt < cfg.minBelsForGridPick) // 不太明白这一段的意义
                loc.x = loc.y = 0;
            if (int(fast_bels.size()) < type_idx + 1)
                fast_bels.resize(type_idx + 1);
            if (int(fast_bels.at(type_idx).size()) < (loc.x + 1))
                fast_bels.at(type_idx).resize(loc.x + 1);
            if (int(fast_bels.at(type_idx).at(loc.x).size()) < (loc.y + 1))
                fast_bels.at(type_idx).at(loc.x).resize(loc.y + 1);
            max_x = std::max(max_x, loc.x);
            max_y = std::max(max_y, loc.y);
            fast_bels.at(type_idx).at(loc.x).at(loc.y).push_back(bel);
        }
        diameter = std::max(max_x, max_y);

        // 获得net信息
        net_bounds.resize(ctx->nets.size());
        net_arc_tcost.resize(ctx->nets.size());
        old_udata.reserve(ctx->nets.size());
        net_by_udata.reserve(ctx->nets.size());
        decltype(NetInfo::udata) n = 0;
        for (auto &net : ctx->nets) {
            old_udata.emplace_back(net.second->udata);            // 获得net的初始元信息
            net_arc_tcost.at(n).resize(net.second->users.size()); // 获得链接信息
            net.second->udata = n++;                              // 更新为布局算法内部元信息
            net_by_udata.push_back(net.second.get());
        }

        // 获得区域信息
        // SAPlacer是默认按照覆盖region内所有bel的最小区域为准，默认是覆盖全局
        for (auto &region : sorted(ctx->region)) {
            Region *r = region.second;
            BoundingBox bb;
            if (r->constr_bels) {
                bb.x0 = std::numeric_limits<int>::max();
                bb.x1 = std::numeric_limits<int>::min();
                bb.y0 = std::numeric_limits<int>::max();
                bb.y1 = std::numeric_limits<int>::min();
                for (auto bel : r->bels) {
                    Loc loc = ctx->getBelLocation(bel);
                    bb.x0 = std::min(bb.x0, loc.x);
                    bb.x1 = std::max(bb.x1, loc.x);
                    bb.y0 = std::min(bb.y0, loc.y);
                    bb.y1 = std::max(bb.y1, loc.y);
                }
            } else {
                bb.x0 = 0;
                bb.y0 = 0;
                bb.x1 = max_x;
                bb.y1 = max_y;
            }
            region_bounds[r->name] = bb;
        }
    }

    ~ForcePlacer()
    {
        for (auto &net : ctx->nets)
            net.second->udata = old_udata[net.second->udata]; // 恢复net的原始udata
    }

    // 建立cell port -> user index 的映射
    void build_port_index()
    {
        for (auto net : sorted(ctx->nets)) {
            NetInfo *ni = net.second;
            for (size_t i = 0; i < ni->users.size(); i++) {
                auto &usr = ni->users.at(i);
                fast_port_to_user[&(usr.cell->ports.at(usr.port))] = i;
            }
        }
    }

    // 布局算法
    bool place()
    {
        log_break();
        ctx->lock();

        size_t placed_cells_count = 0;
        // std::vector<CellInfo *> autoplaced;
        std::vector<CellInfo *> chain_basis;

        // 初始化placer
        // 实际上是在处理约束文件规定了放置位置的CELL
        for (auto &cell_entry : ctx->cells) {
            CellInfo *cell = cell_entry.second.get();
            auto loc = cell->attrs.find(ctx->id("BEL"));
            if (loc != cell->attrs.end()) {
                std::string loc_name = loc->second.as_string();   // 得到当前cell的bel位置属性
                BelId bel = ctx->getBelByName(ctx->id(loc_name)); // 根据位置属性找到bel的类型
                if (bel == BelId()) {
                    // 如果这个Bel是空的，说明板子上没有对应的Bel
                    log_error("No Bel named \'%s\' located for this chip (processing BEL attribute on \'%s\')\n",
                              loc_name.c_str(), cell->name.c_str(ctx));
                }

                IdString bel_type = ctx->getBelType(bel); // 根据belId找到唯一标识符IdString
                if (bel_type != cell->type) {
                    // cell所需的bel类型和当前所处bel类型不匹配
                    log_error("Bel \'%s\' of type \'%s\' does not match cell \'%s\' of type \'%s\'\n", loc_name.c_str(),
                              bel_type.c_str(ctx), cell->name.c_str(ctx), cell->type.c_str(ctx));
                }
                if (!ctx->isValidBelForCell(cell, bel)) {
                    // 判断位置是否合法，比如这个位置以及被其他的Cell占据
                    log_error("Bel \'%s\' of type \'%s\' is not valid for cell \'%s\' of type \'%s\'\n",
                              loc_name.c_str(), bel_type.c_str(ctx), cell->name.c_str(ctx), cell->type.c_str(ctx));
                }

                auto bound_cell = ctx->getBoundBelCell(bel);
                if (bound_cell) {
                    // 当前的cell不能是布局过的
                    log_error("Cell \'%s\' cannot be bound to BEL \'%s\' since it is already bound to cell \'%s\'\n",
                              cell->name.c_str(ctx), loc_name.c_str(), bound_cell->name.c_str(ctx));
                }
                ctx->bindBel(bel, cell, STRENGTH_USER);
                placed_cells_count++;
                locked_bels.insert(bel);
                cell_locs[cell->name] = CellLocation(ctx->getBelLocation(cell->bel));
                cell_locs[cell->name].locked = true;
                cell_locs[cell->name].global = ctx->getBelGlobalBuf(cell->bel);
            }
        }

        log_info("Placed %d cells based on constraints.\n", int(placed_cells_count));
        ctx->yield();

        seedPlacement();
        updateAllChain();
        log_info("Creating initial placement for remaining %d cells.\n", int(place_cells.size()));
        auto place_start_time_anchor_point = std::chrono::high_resolution_clock::now(); // 开始计时锚点

        // 暂时不确定用途，应该是计算时序约束
        if (cfg.budgetBased && cfg.slack_redist_iter > 0)
            assign_budget(ctx);

        ctx->yield();
        auto place_end_time_anchor_point = std::chrono::high_resolution_clock::now(); // 结束计时锚点
        log_break();
        log_info("Initial placement time %.2fs.\n",
                 std::chrono::duration<float>(place_end_time_anchor_point - place_start_time_anchor_point).count());
        // placer初始化结束
        // =========================================================================================================
#if 0
        // 验证cell_locs的位置都正确赋值了
        for (auto &cell : sorted(ctx->cells)) {
            CellInfo *ci = cell.second;
            Loc loc = ctx->getBelLocation(ci->bel);
            CellLocation cloc = cell_locs[cell.first];
            if (cloc.x != loc.x || cloc.y != loc.y)
                log_error("cell %s actually in (%d, %d) but saved (%d, %d) in cell_locs.\n", ci->name.c_str(ctx), loc.x,
                          loc.y, cloc.x, cloc.y);
        }
#endif
        // =========================================================================================================
        // placer正式算法开始
        place_start_time_anchor_point = std::chrono::high_resolution_clock::now();
        if (!cfg.budgetBased)
            get_criticalities(ctx, &net_crit);

        // 初始化代价查找表
        setupCost();
        // 计算线长开销与延迟开销
        curr_wirelen_cost = totalWirelenCost();
        curr_timing_cost = totalTimingCost();
        log_info("random placement wirelen = %ld.\n", curr_wirelen_cost);
        last_wirelen_cost = curr_wirelen_cost;
        last_timing_cost = curr_timing_cost;

        // if (cfg.netShareWeight > 0)
        //     setupNetsByTile()

        wirelen_t avg_wirelen = curr_wirelen_cost;
        wirelen_t min_wirelen = curr_wirelen_cost;

        int n_no_progress = 0;
        bool improved = false;
        // 算法主循环逻辑
        log_info("Runing Force placer.\n");
        for (int iter = 1;; iter++) {
            updateAllNetStar();
            solveAllCellPosition();
            legalisePlacementStrict();
            curr_wirelen_cost = totalWirelenCost();
            log_info("iter %3d: wirelength: %ld.\n", iter, curr_wirelen_cost);
            improved = curr_wirelen_cost < last_wirelen_cost;
            last_wirelen_cost = curr_wirelen_cost;
            if (!improved)
                break;
            ctx->yield();
        }
        legalisePlacementStrict(true);

        place_end_time_anchor_point = std::chrono::high_resolution_clock::now();
        log_break();
        log_info("Force placement time: %.2fs.\n",
                 std::chrono::duration<float>(place_end_time_anchor_point - place_start_time_anchor_point).count());
        log_info("  of legalisation: %.2fs\n", legalise_time);

        curr_wirelen_cost = totalWirelenCost();
        log_break();
        log_info("Force placement wirelen = %ld.\n", curr_wirelen_cost);
        ctx->yield();

        // 最后检查布局合法性
        for (auto bel : ctx->getBels()) {
            CellInfo *cell = ctx->getBoundBelCell(bel);
            if (!ctx->isBelLocationValid(bel)) {
                std::string cell_text = "no cell";
                if (cell != nullptr)
                    cell_text = std::string("cell \'") + ctx->nameOf(cell) + "\'";
                if (ctx->force) {
                    log_warning("placement validity check failed for Bel \'%s\' (%s)\n",
                                ctx->getBelName(bel).c_str(ctx), cell_text.c_str());
                } else {
                    log_error("placement validity check failed for Bel \'%s\' (%s)\n", ctx->getBelName(bel).c_str(ctx),
                              cell_text.c_str());
                }
            }
        }
        for (auto cell : sorted(ctx->cells)) {
            if (get_constraints_distance(ctx, cell.second) != 0)
                log_error("constraint satisfaction check failed for cell \'%s\' at Bel \'%s\'.\n",
                          cell.first.c_str(ctx), ctx->getBelName(cell.second->bel).c_str(ctx));
        }
        timing_analysis(ctx);
        log_info("Final placement valided check done.\n");

        ctx->unlock();

        auto placer1_cfg = Placer1Cfg(ctx);
        placer1_cfg.hpwl_scale_x = cfg.hpwl_scale_x;
        placer1_cfg.hpwl_scale_y = cfg.hpwl_scale_y;
        placer1_refine(ctx, placer1_cfg);

        return true;
    }

  private:
    // 合法化过程，在布局算法运行后执行
    void legalisePlacementStrict(bool require_validity = false)
    {
        bool debug_this = false;
        auto legalise_start_time_anchor_point = std::chrono::high_resolution_clock::now();

        // 解除所有绑定，务必注意不要把约束文件定义的结果解绑
        std::queue<IdString> remaining; // 记录不合法的对象
        for (auto cell : sorted(ctx->cells)) {
            CellInfo *ci = cell.second;
            if (ci->bel != BelId() && (ci->belStrength < STRENGTH_USER)) {
                ctx->unbindBel(ci->bel);
                remaining.push(ci->name);
            }
        }

        // 暂时采用贪心策略
        // TODO 将来采用更高级的合法化过程
        int ripup_radius = 2; // 搜索范围
        int total_iters = 0;
        int total_iters_noreset = 0;
        const int solve_problems = int(remaining.size()); // 要解决的问题大小
        while (!remaining.empty()) {
            auto top = remaining.front();
            remaining.pop();

            CellInfo *ci = ctx->cells.at(top).get();
            CellLocation cloc = cell_locs[ci->name];
            if (ci->bel != BelId())
                continue;
            if (debug_this)
                log_info(" Legalising %s (%s).\n", top.c_str(ctx), ci->type.c_str(ctx));
            int bt = std::get<0>(bel_types.at(ci->type));
            auto &fb = fast_bels[bt];
            int radius = 0;
            int iter = 0;
            int iter_at_radius = 0;
            bool placed = false;
            BelId best_bel;
            int best_inp_len = std::numeric_limits<int>::max();

            if (debug_this)
                std::cerr << " ==> placing cell " << ci->name.c_str(ctx) << std::endl;

            total_iters++;
            total_iters_noreset++;

            if (total_iters > solve_problems) {
                total_iters = 0;
                ripup_radius = std::max(std::max(max_x, max_y), ripup_radius << 1);
            }

            if (total_iters_noreset > std::max(5000, 8 * int(ctx->cells.size()))) {
                log_error("Unable to find legal placement for all cells, design is probably at utilisation limit.\n");
            }

            while (!placed) {
                if (iter > std::max(3000, 3 * int(ctx->cells.size())))
                    log_error("Unable to find legal placement for cell \'%s\', check constraints and utilisation.\n",
                              ctx->nameOf(ci));

                int rx = radius, ry = radius;

                if (ci->region != nullptr) {
                    // 有区域约束
                    rx = std::min(radius,
                                  (region_bounds[ci->region->name].x1 - region_bounds[ci->region->name].x0) / 2 + 1);
                    ry = std::min(radius,
                                  (region_bounds[ci->region->name].y1 - region_bounds[ci->region->name].y0) / 2 + 1);
                }
                // 随机找到约束范围内的一个BEL

                int nx = ctx->rng((rx << 1) + 1) + std::max(cloc.x - rx, 0);
                int ny = ctx->rng((ry << 1) + 1) + std::max(cloc.y - ry, 0);

                iter++;
                iter_at_radius++;
                if (iter >= (10 * (radius + 1))) {
                    // 范围越大搜索的次数越多
                    radius = std::min(std::max(max_x, max_y), radius + 1); // 增加搜索范围
                    while (radius < std::max(max_x, max_y)) {
                        for (int x = std::max(0, cloc.x - radius); x <= std::min(max_x, cloc.x + radius); x++) {
                            if (x >= int(fb.size()))
                                break;
                            for (int y = std::max(0, cloc.y - radius); y <= std::min(max_y, cloc.y + radius); y++) {
                                if (y >= int(fb.at(x).size()))
                                    break;
                                if (fb.at(x).at(y).size() > 0)
                                    goto notempty;
                            }
                        }
                        radius = std::min(std::max(max_x, max_y), radius + 1);
                    }
                notempty:
                    iter_at_radius = 0;
                    iter = 0;
                }
                // 判断是否符合位置
                if (nx < 0 || nx > max_x)
                    continue;
                if (ny < 0 || ny > max_y)
                    continue;
                if (nx >= int(fb.size()))
                    continue;
                if (ny >= int(fb.at(nx).size()))
                    continue;
                if (fb.at(nx).at(ny).empty())
                    continue;

                // 不明白，从heap算法抄过来的
                int need_to_explore = 2 * radius;

                if (iter_at_radius >= need_to_explore && best_bel != BelId()) {
                    // 多次未找到合适的位置尝试清理已经占用的BEL，被清理的BEL重新找
                    CellInfo *bound = ctx->getBoundBelCell(best_bel);
                    if (bound != nullptr) {
                        ctx->unbindBel(bound->bel);
                        remaining.push(bound->name);
                    }
                    ctx->bindBel(best_bel, ci, STRENGTH_WEAK);
                    placed = true;
                    Loc loc = ctx->getBelLocation(best_bel);
                    cell_locs[ci->name].x = loc.x;
                    cell_locs[ci->name].y = loc.y;
                    break;
                }

                if (ci->constr_children.empty() && !ci->constr_abs_z) {
                    for (auto sz : fb.at(nx).at(ny)) {
                        if (ci->region != nullptr && ci->region->constr_bels && !ci->region->bels.count(sz))
                            continue;
                        if (ctx->checkBelAvail(sz) || (radius > ripup_radius || ctx->rng(20000) < 10)) {
                            CellInfo *bound = ctx->getBoundBelCell(sz);
                            if (bound != nullptr) {
                                if (bound->constr_parent != nullptr || !bound->constr_children.empty() ||
                                    bound->constr_abs_z)
                                    continue;
                                ctx->unbindBel(bound->bel);
                            }
                            ctx->bindBel(sz, ci, STRENGTH_WEAK);
                            if (require_validity && !ctx->isBelLocationValid(sz)) {
                                ctx->unbindBel(sz);
                                if (bound != nullptr)
                                    ctx->bindBel(sz, bound, STRENGTH_WEAK);
                            } else if (iter_at_radius < need_to_explore) {
                                // 找移动距离最小的BEL
                                ctx->unbindBel(sz);
                                if (bound != nullptr)
                                    ctx->bindBel(sz, bound, STRENGTH_WEAK);
                                int input_len = 0;
                                for (auto &port : ci->ports) {
                                    auto &p = port.second;
                                    if (p.type != PORT_IN || p.net == nullptr || p.net->driver.cell == nullptr)
                                        continue;
                                    CellInfo *drv = p.net->driver.cell;
                                    auto drv_loc = cell_locs.find(drv->name);
                                    if (drv_loc == cell_locs.end())
                                        continue;
                                    if (drv_loc->second.global)
                                        continue;
                                    input_len = std::abs(drv_loc->second.x - nx) + std::abs(drv_loc->second.y - ny);
                                }
                                if (input_len < best_inp_len) {
                                    best_inp_len = input_len;
                                    best_bel = sz;
                                }
                                break;
                            } else {
                                if (bound != nullptr)
                                    remaining.emplace(bound->name);
                                Loc loc = ctx->getBelLocation(sz);
                                cell_locs[ci->name].x = loc.x;
                                cell_locs[ci->name].y = loc.y;
                                if (debug_this)
                                    std::cerr << " ==> placed w/o constraints! \n";
                                placed = true;
                                break;
                            }
                        }
                    }
                } else {
                    for (auto sz : fb.at(nx).at(ny)) {
                        Loc loc = ctx->getBelLocation(sz);
                        if (ci->constr_abs_z && loc.z != ci->constr_z)
                            continue;
                        std::vector<std::pair<CellInfo *, BelId>> targets;
                        std::vector<std::pair<BelId, CellInfo *>> swaps_made;
                        std::queue<std::pair<CellInfo *, Loc>> visit;
                        visit.emplace(ci, loc);
                        while (!visit.empty()) {
                            CellInfo *vc = visit.front().first;
                            NPNR_ASSERT(vc->bel == BelId());
                            Loc ploc = visit.front().second;
                            visit.pop();
                            BelId target = ctx->getBelByLocation(ploc);
                            if (vc->region != nullptr && vc->region->constr_bels && !vc->region->bels.count(target))
                                goto fail;
                            CellInfo *bound;
                            if (target == BelId() || ctx->getBelType(target) != vc->type)
                                goto fail;
                            bound = ctx->getBoundBelCell(target);
                            // 链不可重叠
                            if (bound != nullptr)
                                if (bound->constr_z != bound->UNCONSTR || bound->constr_parent != nullptr ||
                                    !bound->constr_children.empty() || bound->belStrength > STRENGTH_WEAK)
                                    goto fail;
                            targets.emplace_back(vc, target);
                            for (auto child : vc->constr_children) {
                                Loc cloc = ploc;
                                if (child->constr_x != child->UNCONSTR)
                                    cloc.x += child->constr_x;
                                if (child->constr_y != child->UNCONSTR)
                                    cloc.y += child->constr_y;
                                if (child->constr_z != child->UNCONSTR)
                                    cloc.z = child->constr_abs_z ? child->constr_z : (ploc.z + child->constr_z);
                                visit.emplace(child, cloc);
                            }
                        }

                        for (auto &target : targets) {
                            CellInfo *bound = ctx->getBoundBelCell(target.second);
                            if (bound != nullptr)
                                ctx->unbindBel(target.second);
                            ctx->bindBel(target.second, target.first, STRENGTH_STRONG);
                            swaps_made.emplace_back(target.second, bound);
                        }

                        for (auto &sm : swaps_made) {
                            if (!ctx->isBelLocationValid(sm.first)) {
                                if (debug_this)
                                    std::cerr << " ==> fail: move is illegal. \n";
                                goto fail;
                            }
                        }
                        if (false) {
                            // 发生错误时恢复原状
                        fail:
                            for (auto &swap : swaps_made) {
                                ctx->unbindBel(swap.first);
                                if (swap.second != nullptr)
                                    ctx->bindBel(swap.first, swap.second, STRENGTH_WEAK);
                            }
                            continue;
                        }
                        for (auto &target : targets) {
                            Loc loc = ctx->getBelLocation(target.second);
                            cell_locs[target.first->name].x = loc.x;
                            cell_locs[target.first->name].y = loc.y;
                            if (debug_this)
                                log_info("%s %d %d %d\n", target.first->name.c_str(ctx), loc.x, loc.y, loc.z);
                        }
                        for (auto &swap : swaps_made) {
                            if (swap.second != nullptr)
                                remaining.emplace(swap.second->name);
                        }

                        if (debug_this)
                            std::cerr << " ==> placed with constraints! \n";
                        placed = true;
                        break;
                    }
                }
            }
        }
        auto legalise_end_time_anchor_point = std::chrono::high_resolution_clock::now();
        legalise_time +=
                std::chrono::duration<float>(legalise_end_time_anchor_point - legalise_start_time_anchor_point).count();
    }

    // 随机初始化放置
    void seedPlacement()
    {
        std::unordered_map<IdString, std::deque<BelId>> available_bels;
        for (auto bel : ctx->getBels()) {
            if (!ctx->checkBelAvail(bel))
                continue;
            available_bels[ctx->getBelType(bel)].push_back(bel);
        }
        for (auto &t : available_bels) {
            std::random_shuffle(t.second.begin(), t.second.end(), [&](size_t n) { return ctx->rng(int(n)); });
        }
        for (auto cell : sorted(ctx->cells)) {
            CellInfo *ci = cell.second;
            if (ci->bel != BelId()) {
                Loc loc = ctx->getBelLocation(ci->bel);
                CellLocation cloc(loc);
                cloc.locked = true;
                cloc.global = ctx->getBelGlobalBuf(ci->bel);
                cell_locs[ci->name] = cloc;
            } else if (ci->constr_parent == nullptr) {
                bool placed = false;
                while (!placed) {
                    if (!available_bels.count(ci->type) || available_bels.at(ci->type).empty())
                        log_error("Unable to place cell \'$%s\', no Bels remaining of type \'%s\'.\n",
                                  ci->name.c_str(ctx), ci->type.c_str(ctx));
                    BelId bel = available_bels.at(ci->type).back();
                    available_bels.at(ci->type).pop_back();
                    Loc loc = ctx->getBelLocation(bel);
                    CellLocation cloc(loc);
                    cloc.locked = false;
                    cloc.global = ctx->getBelGlobalBuf(bel);
                    cell_locs[ci->name] = cloc;
                    if (hasMeanfulConnectivity(ci) && !cfg.ioBufTypes.count(ci->type)) {
                        place_cells.push_back(ci);
                        placed = true;
                        ctx->bindBel(bel, ci, STRENGTH_WEAK);
                    } else {
                        if (ctx->isValidBelForCell(ci, bel)) {
                            ctx->bindBel(bel, ci, STRENGTH_STRONG);
                            cell_locs[ci->name].locked = true;
                            placed = true;
                        } else {
                            available_bels.at(ci->type).push_front(bel);
                        }
                    }
                }
            }
        }
    }

    // 初始化代价 map
    void setupCost()
    {
        for (auto net : sorted(ctx->nets)) {
            NetInfo *ni = net.second;
            // FIXME 移动到ignoreNet判断之后会导致updateNetStar出现段错误，即访问了属于ignoreNet的net
            net_star_infos[ni->name] = NetStar();
            net_star_infos[ni->name].net_len = int(ni->users.size());
            net_star_infos[ni->name].net_len += ni->driver.cell == nullptr ? 0 : 1;
            if (ignoreNet(ni)) // 不需要关心的net
                continue;
            net_bounds[ni->udata] = getNetBounds(ni);
            if (cfg.timing_driven && int(ni->users.size()) < cfg.timingFanoutThresh)
                for (size_t i = 0; i < ni->users.size(); i++)
                    net_arc_tcost[ni->udata][i] = getTimingCost(ni, i);
        }
    }

    // 计算net中到特定端口的延迟
    inline double getTimingCost(NetInfo *net, size_t user)
    {
        int cc;
        if (net->driver.cell == nullptr)
            return 0;
        if (ctx->getPortTimingClass(net->driver.cell, net->driver.port, cc) == TMG_IGNORE)
            return 0;
        if (cfg.budgetBased) {
            double delay = ctx->getDelayNS(ctx->predictDelay(net, net->users.at(user)));
            return std::min(10.0, std::exp(delay - ctx->getDelayNS(net->users.at(user).budget) / 10));
        }
        auto crit = net_crit.find(net->name); // 找到延迟惩罚项
        if (crit == net_crit.end() || crit->second.criticality.empty())
            return 0;
        double delay = ctx->getDelayNS(ctx->predictDelay(net, net->users.at(user)));
        return delay * std::pow(crit->second.criticality.at(user), crit_exp);
    }

    // 计算net的最小包围盒
    inline BoundingBox getNetBounds(NetInfo *net)
    {
        BoundingBox bb;
        NPNR_ASSERT(net->driver.cell != nullptr);
        Loc dloc = ctx->getBelLocation(net->driver.cell->bel);
        bb.x0 = dloc.x;
        bb.x1 = dloc.x;
        bb.y0 = dloc.y;
        bb.y1 = dloc.y;
        bb.nx0 = 1;
        bb.nx1 = 1;
        bb.ny0 = 1;
        bb.ny1 = 1;
        for (auto user : net->users) {
            if (user.cell->bel == BelId())
                continue;
            Loc uloc = ctx->getBelLocation(user.cell->bel);
            if (uloc.x == bb.x0)
                bb.nx0++;
            else if (uloc.x < bb.x0) {
                bb.x0 = uloc.x;
                bb.nx0 = 1;
            }
            if (uloc.x == bb.x1)
                bb.nx1++;
            else if (uloc.x > bb.x1) {
                bb.x1 = uloc.x;
                bb.nx1 = 1;
            }
            if (uloc.y == bb.y0)
                bb.ny0++;
            else if (uloc.y < bb.y0) {
                bb.y0 = uloc.y;
                bb.ny0 = 1;
            }
            if (uloc.y == bb.y1)
                bb.ny1++;
            else if (uloc.y > bb.y1) {
                bb.y1 = uloc.y;
                bb.ny1 = 1;
            }
        }
        return bb;
    }

    // 判断net是否有记录代价的必要，比如没有驱动port的net就没有意义
    inline bool ignoreNet(NetInfo *net)
    {
        return net->driver.cell == nullptr || net->driver.cell->bel == BelId() ||
               ctx->getBelGlobalBuf(net->driver.cell->bel);
    }

    bool hasMeanfulConnectivity(CellInfo *cell)
    {
        for (auto port : cell->ports) {
            if (port.second.net != nullptr && port.second.net->driver.cell != nullptr &&
                !port.second.net->users.empty())
                return true;
        }
        return false;
    }

    // 计算总线长开销
    wirelen_t totalWirelenCost()
    {
        wirelen_t cost = 0;
        for (const auto &net : sorted(ctx->nets)) {
            NetInfo *ni = net.second;
            if (ni->driver.cell == nullptr)
                continue;
            CellLocation &drvloc = cell_locs.at(ni->driver.cell->name);
            if (drvloc.global)
                continue;
            int xmin = drvloc.x, xmax = drvloc.x, ymin = drvloc.y, ymax = drvloc.y;
            for (auto &user : ni->users) {
                CellLocation &usrloc = cell_locs.at(user.cell->name);
                xmin = std::min(xmin, usrloc.x);
                xmax = std::max(xmax, usrloc.x);
                ymin = std::min(ymin, usrloc.y);
                ymax = std::max(ymax, usrloc.y);
            }
            cost += cfg.hpwl_scale_x * (xmax - xmin) + cfg.hpwl_scale_y * (ymax - ymin);
        }
        return cost;
    }

    // 计算延迟开销
    double totalTimingCost()
    {
        double cost = 0.0f;
        for (const auto &net : net_arc_tcost) {
            for (auto arc_cost : net) {
                cost += arc_cost;
            }
        }
        return cost;
    }

#if 1
    // 更新链接的子节点
    void updateChain(CellInfo *cell, CellInfo *root)
    {
        const auto &base = cell_locs[cell->name];
        for (auto child : cell->constr_children) {
            if (child->type == root->type) // 更新 chain_size 的，在合法化时优先处理更大 chain_size 的对象
                chain_size[root->name] += 1;
            if (child->constr_x != child->UNCONSTR)
                cell_locs[child->name].x = std::max(0, std::min(max_x, base.x + child->constr_x));
            else
                cell_locs[child->name].x = base.x;
            if (child->constr_y != child->UNCONSTR)
                cell_locs[child->name].y = std::max(0, std::min(max_y, base.y + child->constr_y));
            else
                cell_locs[child->name].y = base.y;
            chain_root[child->name] = root;
            if (!child->constr_children.empty())
                updateChain(child, root);
        }
    }

    // 自动更新所有的chain上信息
    void updateAllChain()
    {
        // TODO 需要增加可移动cell的统计，只包含chain-root和非fixed的对象
        for (auto cell : place_cells) {
            chain_size[cell->name] = 1;
            if (!cell->constr_children.empty())
                updateChain(cell, cell);
        }
    }
#endif

    // 更新net的分布中心点信息和散度信息
    void updateNetStar(NetInfo *net)
    {
        // if (net == nullptr || net->driver.cell != nullptr || net->users.empty())
        if (net == nullptr)
            return;
        NetStar &ns = net_star_infos.at(net->name);
        double square_x_sum = 0.0, square_y_sum = 0.0; // sum(x_i^2)
        double x_sum = 0.0, y_sum = 0;                 // sum(x_i)
        if (net->driver.cell != nullptr) {
            CellInfo *ci = net->driver.cell;
            CellLocation cloc = cell_locs[ci->name];
            square_x_sum = double(cloc.x * cloc.x);
            square_y_sum = double(cloc.y * cloc.y);
            x_sum = double(cloc.x);
            y_sum = double(cloc.y);
        }
        for (const auto &cell : net->users) {
            CellInfo *ci = cell.cell;
            CellLocation cloc = cell_locs[ci->name];
            square_x_sum += double(cloc.x * cloc.x);
            square_y_sum += double(cloc.y * cloc.y);
            x_sum += double(cloc.x);
            y_sum += double(cloc.y);
        }
        NPNR_ASSERT(cfg.phi > 0);
        NPNR_ASSERT(cfg.gamma > 0);
        ns.x_divergence = std::sqrt(square_x_sum - x_sum * x_sum / double(ns.net_len) + cfg.phi) * cfg.gamma;
        ns.y_divergence = std::sqrt(square_y_sum - y_sum * y_sum / double(ns.net_len) + cfg.phi) * cfg.gamma;
        ns.xc = x_sum / double(ns.net_len);
        ns.yc = y_sum / double(ns.net_len);
    }

    // 更新所有net的star算法信息
    void updateAllNetStar()
    {
        for (const auto &net : sorted(ctx->nets)) {
            NetInfo *ni = net.second;
            if (ni == nullptr || ni->driver.cell == nullptr || ni->driver.cell->bel == BelId())
                continue;
            updateNetStar(ni);
        }
    }

    // 求解单个cell的新位置
    void solveCellPosition(CellInfo *cell)
    {
        CellLocation &cloc = cell_locs[cell->name];
        double net_divergence_sum_x = 0.0, net_divergence_sum_y = 0.0;
        double next_rawx = 0.0, next_rawy = 0.0;
        for (auto port : cell->ports) {
            PortInfo pi = port.second;
            NetInfo *ni = pi.net;
            if (ni == nullptr || ni->driver.cell == nullptr || ni->driver.cell->bel == BelId())
                continue;
            NetStar ns = net_star_infos[ni->name];
            next_rawx += ns.xc / ns.x_divergence;
            next_rawy += ns.yc / ns.y_divergence;
            net_divergence_sum_x += 1.0 / ns.x_divergence;
            net_divergence_sum_y += 1.0 / ns.y_divergence;
        }
        NPNR_ASSERT(net_divergence_sum_x > 0);
        NPNR_ASSERT(net_divergence_sum_y > 0);
        cloc.rawx = next_rawx / net_divergence_sum_x;
        cloc.rawy = next_rawy / net_divergence_sum_y;

        cloc.x = int(cloc.rawx);
        cloc.y = int(cloc.rawy);
    }

    // 更新所有cell的新位置
    void solveAllCellPosition()
    {
        for (auto cell : place_cells) {
            if (cell_locs.at(cell->name).global)
                continue;
            solveCellPosition(cell);
        }
    }

    // 基本信息
    Context *ctx;
    PlacerFCfg cfg;
    float crit_exp = 8.0f;
    wirelen_t curr_wirelen_cost, last_wirelen_cost;
    double last_timing_cost, curr_timing_cost;
    float legalise_time = 0.0f;

    int diameter = 35, max_x = 1, max_y = 1; // diameter 控制交换空间范围，不确定是否有必要保留
    // 部分网络限制其边界框大小，从而跳过移动到边界框外的无效步骤
    std::vector<BoundingBox> net_bounds;
    std::unordered_map<IdString, NetStar> net_star_infos;
    // 部分线网的时钟惩罚（criticality * delay ns）
    std::vector<std::vector<double>> net_arc_tcost;

    std::unordered_map<IdString, std::tuple<int, int>> bel_types;
    std::unordered_map<IdString, BoundingBox> region_bounds;

    // 记录节点的位置
    std::unordered_map<IdString, CellLocation> cell_locs;
    // 记录链chain上的节点所属链的根节点
    std::unordered_map<IdString, CellInfo *> chain_root;
    // 记录链chain上的节点所属链的大小，较大的优先进行合法化放置
    std::unordered_map<IdString, int> chain_size;
    // 真正会尝试布局的CELL对象，只包含非lock的宏块
    std::vector<CellInfo *> place_cells;

    std::unordered_map<const PortInfo *, size_t>
            fast_port_to_user; // 给定port的信息快速查找这个port在net中连接点下标，从而根据net中usr数组访问对应的port
    std::vector<std::vector<std::vector<std::vector<BelId>>>> fast_bels;
    std::unordered_set<BelId> locked_bels;

    std::vector<decltype(NetInfo::udata)> old_udata;
    std::vector<NetInfo *> net_by_udata;

    // Criticality data from timing analysis
    NetCriticalityMap net_crit;
};

PlacerFCfg::PlacerFCfg(Context *ctx)
{
    minBelsForGridPick = ctx->setting<int>("placerforce/minBelsForGridPick", 64);
    hpwl_scale_x = 1;
    hpwl_scale_y = 1;
}

bool placer_force(Context *ctx, PlacerFCfg cfg)
{
    try {
        ForcePlacer placer(ctx, cfg);
        placer.place();
        log_info("Checksum: 0x%08x\n", ctx->checksum());
#ifndef NDEBUG
        ctx->lock();
        ctx->check();
        ctx->unlock();
#endif
        return true;
    } catch (log_execution_error_exception) {
#ifndef NDEBUG
        ctx->check();
#endif
        return false;
    }
}

NEXTPNR_NAMESPACE_END