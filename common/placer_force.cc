

#include "placer_force.h"
#include <algorithm>
#include <chrono>
#include <map>
#include <numeric>
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
        int x, y;                       // 当前位置
        int legal_x, legal_y;           // 合法化位置
        double rawx, rawy;              // 力算法得到的原始位置
        int best_legal_x, best_legal_y; // 最优合法化位置
        bool locked = false, global = false;

        CellLocation()
        {
            x = y = 0;
            rawx = rawy = 0;
            legal_x = legal_y = 0;
        }
        CellLocation(Loc loc)
        {
            x = loc.x;
            y = loc.y;
            rawx = double(x);
            rawy = double(y);
            legal_x = 0;
            legal_y = 0;
        }
        void legal()
        {
            legal_x = x;
            legal_y = y;
        }
        void bestLegal()
        {
            best_legal_x = legal_x;
            best_legal_y = legal_y;
        }
    };

    // Star算法中间变量
    struct NetStar
    {
        double xc, yc;                     // 线网的平均中心，xc = sum(x_i) / len(net) ，其中x_i为所有相连port的位置
        double x_divergence, y_divergence; // Divergence = \sqrt{sum((x_i - xc)^2) + 1} ，参考star+算法的S变量
        int net_len;                       // net中链接的Cell数量
        double x_weight, y_weight;         // 权重
    };

  public:
    ForcePlacer(Context *ctx, PlacerFCfg cfg) : ctx(ctx), cfg(cfg) { buildFastBels(); }

    ~ForcePlacer() {}

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
                cell_locs[cell->name] = CellLocation(ctx->getBelLocation(cell->bel));
                cell_locs[cell->name].locked = true;
                cell_locs[cell->name].global = ctx->getBelGlobalBuf(cell->bel);
            }
        }

        log_info("Placed %d cells based on constraints.\n", int(placed_cells_count));
        ctx->yield();

        seedPlacement();
        updateAllChain();
        setupStar();
        log_info("Creating initial placement for remaining %d cells, random placement wirelen = %ld.\n",
                 int(place_cells.size()), totalWirelenCost());
        auto place_start_time_anchor_point = std::chrono::high_resolution_clock::now(); // 开始计时锚点

        // 暂时不确定用途，应该是计算时序约束
        if (cfg.timeDriven && cfg.slack_redist_iter > 0)
            assign_budget(ctx);
        setupSolveCells();
#if 1
        for (int i = 0; i < 5; i++) {
            updateAllNetStar();
            solveAllCellPosition();
            updateAllChain();
            log_info("  at initial placer iter #%3d, wirelen = %ld.\n", i, totalWirelenCost());
        }
#endif
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

        // 计算线长开销与延迟开销
        curr_wirelen_cost = totalWirelenCost();

        log_info("random placement wirelen = %ld.\n", curr_wirelen_cost);
        last_timing_cost = curr_timing_cost;
        best_wirelen_cost = std::numeric_limits<int64_t>::max();

        wirelen_t solve_wirelen = curr_wirelen_cost;
        wirelen_t spread_wirelen = curr_wirelen_cost;
        wirelen_t legal_wirelen = curr_wirelen_cost;

        std::unordered_set<IdString> all_celltype;
        for (auto cell : place_cells)
            all_celltype.insert(cell->type);

        int n_no_progress = 0;
        // 算法主循环逻辑
        log_info("Runing Force placer.\n");
        for (int iter = 1;; iter++) {
            auto solve_time_start_anchor_point = std::chrono::high_resolution_clock::now();
            auto iter_time_start_anchor_point = solve_time_start_anchor_point;
            for (int loop = 0; loop < 3; loop++) {
                updateAllNetStar();             // TODO 扩散后不能及时收缩导致越扩散越开，考虑多次迭代后进行一次合法化
                solveAllCellPosition(iter - 1); // 第一次运行时legal_x和legal_y处于未初始化状态，因此赋值0
                updateAllChain();
                log_info("    at iter-loop #%3d-@%2d, solve wirelength: %ld.\n", iter, loop, totalWirelenCost());
            }
            auto solve_time_end_anchor_point = std::chrono::high_resolution_clock::now();
            solve_time +=
                    std::chrono::duration<float>(solve_time_end_anchor_point - solve_time_start_anchor_point).count();
            solve_wirelen = totalWirelenCost();

            // for (const auto &group : cfg.cellGroups)
            //     CutSpreader(this, group).run();
            // for (auto type : sorted(all_celltype)) {
            //     if (std::all_of(cfg.cellGroups.begin(), cfg.cellGroups.end(),
            //                     [type](const std::unordered_set<IdString> &grp) { return !grp.count(type); }))
            //         CutSpreader(this, {type}).run();
            // }
            updateAllChain();
            spread_wirelen = totalWirelenCost();

            // 合法化
            legalisePlacementStrict(true);
            updateAllChain();
            for (auto &cell : cell_locs)
                cell.second.legal();
            if (cfg.timeDriven)
                get_criticalities(ctx, &net_crit);

            legal_wirelen = totalWirelenCost();
            curr_wirelen_cost = legal_wirelen;
            auto iter_time_end_archor_point = std::chrono::high_resolution_clock::now();
            log_info("  at iter #%3d: solve wirelength: %ld, spread wirelength: %ld, legal wirelength: %ld, time = "
                     "%.3fs.\n",
                     iter, solve_wirelen, spread_wirelen, legal_wirelen,
                     std::chrono::duration<float>(iter_time_end_archor_point - iter_time_start_anchor_point).count());
            if (curr_wirelen_cost < best_wirelen_cost) {
                best_wirelen_cost = curr_wirelen_cost;
                n_no_progress = 0;
                // 保存当前最优解
                for (auto &cell : cell_locs)
                    cell.second.bestLegal();
            } else {
                ++n_no_progress;
            }
            if (n_no_progress >= 5)
                break;
            ctx->yield();
        }
        // 恢复最优解
        for (auto &cell : cell_locs) {
            cell.second.x = cell.second.best_legal_x;
            cell.second.y = cell.second.best_legal_y;
        }
        legalisePlacementStrict(true);

        place_end_time_anchor_point = std::chrono::high_resolution_clock::now();
        log_break();
        log_info("Force placement time: %.2fs.\n",
                 std::chrono::duration<float>(place_end_time_anchor_point - place_start_time_anchor_point).count());
        log_info("  of solving time: %.2fs.\n", solve_time);
        log_info("  of spreading cells: %.2fs.\n", spread_time);
        log_info("  of strict legalisation: %.2fs\n", legalise_time);

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
        const bool debug_this = false;
        auto legalise_start_time_anchor_point = std::chrono::high_resolution_clock::now();

        // 解除所有绑定，务必注意不要把约束文件定义的结果解绑
        for (auto cell : sorted(ctx->cells)) {
            CellInfo *ci = cell.second;
            if (ci->bel != BelId() && (ci->udata != dont_solve ||
                                       (chain_root.count(ci->name) && chain_root.at(ci->name)->udata != dont_solve))) {
                ctx->unbindBel(ci->bel);
            }
        }

        std::priority_queue<std::pair<int, IdString>> remaining;
        for (auto cell : solve_cells)
            remaining.emplace(chain_size[cell->name], cell->name);

        // 暂时采用贪心策略
        // TODO 将来采用更高级的合法化过程
        int ripup_radius = 2; // 搜索范围
        int total_iters = 0;
        int total_iters_noreset = 0;

        while (!remaining.empty()) {
            auto top = remaining.top();
            remaining.pop();

            CellInfo *ci = ctx->cells.at(top.second).get();
            CellLocation cloc = cell_locs[ci->name];
            if (ci->bel != BelId())
                continue;
            if (debug_this)
                log_info(" Legalising %s (%s).\n", ci->name.c_str(ctx), ci->type.c_str(ctx));
            int bt = std::get<0>(bel_types.at(ci->type));
            auto &fb = fast_bels.at(bt);
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
            if (total_iters > int(solve_cells.size())) {
                total_iters = 0;
                ripup_radius = std::max(std::max(max_x, max_y), ripup_radius * 2);
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
                    rx = std::min(radius, (constraint_region_bounds[ci->region->name].x1 -
                                           constraint_region_bounds[ci->region->name].x0) /
                                                          2 +
                                                  1);
                    ry = std::min(radius, (constraint_region_bounds[ci->region->name].y1 -
                                           constraint_region_bounds[ci->region->name].y0) /
                                                          2 +
                                                  1);
                }
                // 随机找到约束范围内的一个BEL

                int nx = ctx->rng(2 * rx + 1) + std::max(cell_locs.at(ci->name).x - rx, 0);
                int ny = ctx->rng(2 * ry + 1) + std::max(cell_locs.at(ci->name).y - ry, 0);

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
                        remaining.emplace(chain_size[bound->name], bound->name);
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
                                    input_len += std::abs(drv_loc->second.x - nx) + std::abs(drv_loc->second.y - ny);
                                }
                                if (input_len < best_inp_len) {
                                    best_inp_len = input_len;
                                    best_bel = sz;
                                }
                                break;
                            } else {
                                if (bound != nullptr)
                                    remaining.emplace(chain_size[bound->name], bound->name);
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
                                remaining.emplace(chain_size[swap.second->name], swap.second->name);
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

    // 建立fast_bel和nearest_row_with_bel和newrest_col_with_bel
    void buildFastBels()
    {
        int num_bel_types = 0;
        for (auto bel : ctx->getBels()) {
            IdString type = ctx->getBelType(bel);
            if (bel_types.find(type) == bel_types.end()) {
                bel_types[type] = std::tuple<int, int>(num_bel_types++, 1);
            } else {
                std::get<1>(bel_types.at(type))++;
            }
        }
        for (auto bel : ctx->getBels()) {
            if (!ctx->checkBelAvail(bel))
                continue;
            Loc loc = ctx->getBelLocation(bel);
            IdString type = ctx->getBelType(bel);
            int type_idx = std::get<0>(bel_types.at(type));
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

        nearest_row_with_bel.resize(num_bel_types, std::vector<int>(max_y + 1, -1));
        nearest_col_with_bel.resize(num_bel_types, std::vector<int>(max_x + 1, -1));
        for (auto bel : ctx->getBels()) {
            if (!ctx->checkBelAvail(bel))
                continue;
            Loc loc = ctx->getBelLocation(bel);
            int type_idx = std::get<0>(bel_types.at(ctx->getBelType(bel)));
            auto &nr = nearest_row_with_bel.at(type_idx), &nc = nearest_col_with_bel.at(type_idx);

            for (int x = loc.x; x <= max_x; x++) {
                if (nc.at(x) != -1 && std::abs(loc.x - nc.at(x)) <= (x - loc.x))
                    break;
                nc.at(x) = loc.x;
            }
            for (int x = loc.x - 1; x >= 0; x--) {
                if (nc.at(x) != -1 && std::abs(loc.x - nc.at(x)) <= (loc.x - x))
                    break;
                nc.at(x) = loc.x;
            }
            for (int y = loc.y; y <= max_y; y++) {
                if (nr.at(y) != -1 && std::abs(loc.y - nr.at(y)) <= (y - loc.y))
                    break;
                nr.at(y) = loc.y;
            }
            for (int y = loc.y - 1; y >= 0; y--) {
                if (nr.at(y) != -1 && std::abs(loc.y - nr.at(y)) <= (loc.y - y))
                    break;
                nr.at(y) = loc.y;
            }
        }

        // bounding box for region constraints
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
            constraint_region_bounds[r->name] = bb;
        }
    }

    // 初始化star算法信息
    void setupStar()
    {
        for (auto net : sorted(ctx->nets)) {
            NetInfo *ni = net.second;
            // FIXME 移动到ignoreNet判断之后会导致updateNetStar出现段错误，即访问了属于ignoreNet的net
            net_star_infos[ni->name] = NetStar();
            net_star_infos[ni->name].net_len = int(ni->users.size());
            net_star_infos[ni->name].net_len += ni->driver.cell == nullptr ? 0 : 1;
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
        if (cfg.timeDriven) {
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

#if 0
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
#endif

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

    // 搜集所有需要布局的模块信息
    int setupSolveCells()
    {
        int row = 0;
        solve_cells.clear();
        // 清除所有cell的udata
        for (auto cell : sorted(ctx->cells))
            cell.second->udata = dont_solve;
        // 更新需要布局cell的udata
        for (auto cell : place_cells) {
            cell->udata = row++;
            solve_cells.push_back(cell);
        }
        // 最后更新子节点
        for (auto chained : chain_root)
            ctx->cells.at(chained.first)->udata = chained.second->udata;
        return row;
    }
#endif

    // HPWL线长估计模型修正因子
    // 源自文献RISA: accurate and efficient placement routability modeling
    double hpwlWightFactor(int size)
    {
        NPNR_ASSERT(size > 0);
        if (size > 0 && size <= 3)
            return 1.0;
        else if (size <= 10) {
            switch (size) {
            case 4:
                return 1.0828;
            case 5:
                return 1.1536;
            case 6:
                return 1.2206;
            case 7:
                return 1.2823;
            case 8:
                return 1.3385;
            case 9:
                return 1.3991;
            case 10:
                return 1.4493;
            };
        } else if (size <= 15)
            return 1.6899;
        else if (size <= 20)
            return 1.8924;
        else if (size <= 25)
            return 2.0743;
        else if (size <= 30)
            return 2.2334;
        else if (size <= 35)
            return 2.3895;
        else if (size <= 40)
            return 2.5356;
        else if (size <= 45)
            return 2.6625;
        return 2.7933;
    }

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
        BoundingBox bb = getNetBounds(net);
        ns.x_weight =
                1 / (hpwlWightFactor(ns.net_len) * (std::max<double>(1.0, cfg.hpwl_scale_x * std::abs(bb.x1 - bb.x0))));
        ns.y_weight =
                1 / (hpwlWightFactor(ns.net_len) * (std::max<double>(1.0, cfg.hpwl_scale_y * std::abs(bb.y1 - bb.y0))));
        for (size_t i = 0; i < net->users.size(); i++) {
            CellInfo *ci = net->users.at(i).cell;
            CellLocation cloc = cell_locs[ci->name];
            square_x_sum += double(cloc.x * cloc.x);
            square_y_sum += double(cloc.y * cloc.y);
            x_sum += double(cloc.x);
            y_sum += double(cloc.y);
            if (net_crit.find(net->name) != net_crit.end()) {
                auto nc = net_crit.at(net->name).criticality;
                if (i < nc.size()) {
                    // nc内部是一些小于1大于0的浮点数
                    double update_weight = 1.0 + cfg.timingWeight * std::pow(nc.at(i), cfg.criticalityExponent);
                    ns.x_weight /= update_weight;
                    ns.y_weight /= update_weight;
                }
            }
        }
        NPNR_ASSERT(cfg.phi > 0);
        NPNR_ASSERT(cfg.gamma > 0);
        ns.x_divergence =
                std::sqrt(square_x_sum - x_sum * x_sum / double(ns.net_len) + cfg.phi) * cfg.gamma * ns.x_weight;
        ns.y_divergence =
                std::sqrt(square_y_sum - y_sum * y_sum / double(ns.net_len) + cfg.phi) * cfg.gamma * ns.y_weight;
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
    void solveCellPosition(CellInfo *cell, int iter)
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
#if 0
        // 参数很难调整，不如选择直接在rawx和rawy的基础上线性组合
        if (iter > 0) {
            double Sxn = std::sqrt(1.0 + std::pow(cloc.rawx - cloc.best_legal_x, 2.0)) * cfg.alpha *
                         (std::max(0.1, double(cfg.hpwl_scale_x * std::abs(cloc.rawx - cloc.best_legal_x)))) /
                         (1.0 * iter);
            double Syn = std::sqrt(1.0 + std::pow(cloc.rawy - cloc.best_legal_y, 2.0)) * cfg.alpha *
                         (std::max(0.1, double(cfg.hpwl_scale_y * std::abs(cloc.rawy - cloc.best_legal_y)))) /
                         (1.0 * iter);
            net_divergence_sum_x += 1.0 / Sxn;
            net_divergence_sum_y += 1.0 / Syn;
            next_rawx += cloc.legal_x / Sxn;
            next_rawy += cloc.legal_y / Syn;
        }
        cloc.rawx = next_rawx / net_divergence_sum_x;
        cloc.rawy = next_rawy / net_divergence_sum_y;
#else
        cloc.rawx = next_rawx / net_divergence_sum_x;
        cloc.rawy = next_rawy / net_divergence_sum_y;
        if (iter > 0) {
            double weight = double(cfg.alpha * iter);
            double weight_x =
                    std::min(1.0, std::max(0.0, weight / std::log10(std::abs(cloc.rawx - cloc.best_legal_x) + 1)));
            double weight_y =
                    std::min(1.0, std::max(0.0, weight / std::log10(std::abs(cloc.rawy - cloc.best_legal_y) + 1)));
            cloc.rawx = (1 - weight_x) * cloc.rawx + weight_x * double(cloc.best_legal_x);
            cloc.rawy = (1 - weight_y) * cloc.rawy + weight_y * double(cloc.best_legal_y);
        }
#endif
        cloc.x = std::round(cloc.rawx);
        cloc.y = std::round(cloc.rawy);
        if (cell->region != nullptr) {
            cloc.x = limit_to_reg(cell->region, cloc.x, false);
            cloc.y = limit_to_reg(cell->region, cloc.y, true);
        }
    }

    // 更新所有cell的新位置
    void solveAllCellPosition(int iter = -1)
    {
        for (auto cell : solve_cells) {
            if (cell_locs.at(cell->name).global || cell_locs.at(cell->name).locked)
                continue;
            solveCellPosition(cell, iter);
        }
    }

    // 基本信息
    Context *ctx;
    PlacerFCfg cfg;
    float crit_exp = 8.0f;
    wirelen_t curr_wirelen_cost, best_wirelen_cost;
    double last_timing_cost, curr_timing_cost;
    float legalise_time = 0.0f, solve_time = 0, spread_time = 0;

    int max_x = 1, max_y = 1;
    std::unordered_map<IdString, NetStar> net_star_infos;

    std::unordered_map<IdString, std::tuple<int, int>> bel_types;
    std::unordered_map<IdString, BoundingBox> constraint_region_bounds;

    // 记录节点的位置
    std::unordered_map<IdString, CellLocation> cell_locs;
    // 记录链chain上的节点所属链的根节点
    std::unordered_map<IdString, CellInfo *> chain_root;
    // 记录链chain上的节点所属链的大小，较大的优先进行合法化放置
    std::unordered_map<IdString, int> chain_size;
    // 真正会尝试布局的CELL对象，只包含非lock的宏块
    std::vector<CellInfo *> place_cells;
    std::vector<CellInfo *> solve_cells;

    std::vector<std::vector<std::vector<std::vector<BelId>>>> fast_bels;
    std::vector<std::vector<int>> nearest_row_with_bel;
    std::vector<std::vector<int>> nearest_col_with_bel;

    // Criticality data from timing analysis
    NetCriticalityMap net_crit;

    decltype(CellInfo::udata) dont_solve = std::numeric_limits<decltype(CellInfo::udata)>::max();

    // 二分元件扩散流程
    template <typename T> T limit_to_reg(Region *reg, T val, bool dir)
    {
        if (reg == nullptr)
            return val;
        int limit_low = dir ? constraint_region_bounds[reg->name].y0 : constraint_region_bounds[reg->name].x0;
        int limit_high = dir ? constraint_region_bounds[reg->name].y1 : constraint_region_bounds[reg->name].x1;
        return std::max<T>(std::min<T>(val, limit_high), limit_low);
    }

    struct ChainExtent
    {
        int x0, x1, y0, y1;
    };

    struct SpreaderRegion
    {
        int id;
        int x0, x1, y0, y1;
        std::vector<int> cells, bels;
        bool overused(float beta) const
        {
            for (size_t t = 0; t < cells.size(); t++) {
                if (bels.at(t) < 4) {
                    if (cells.at(t) > bels.at(t))
                        return true;
                } else {
                    if (cells.at(t) > beta * bels.at(t))
                        return true;
                }
            }
            return false;
        }
    };

    class CutSpreader
    {
      public:
        CutSpreader(ForcePlacer *p, const std::unordered_set<IdString> &beltype) : p(p), ctx(p->ctx), beltype(beltype)
        {
            int idx = 0;
            for (IdString type : sorted(beltype)) {
                type_index[type] = idx;
                fb.emplace_back(p->bel_types.count(type) ? &(p->fast_bels.at(std::get<0>(p->bel_types.at(type))))
                                                         : nullptr);
                idx++;
            }
        }
        static int seq;
        void run()
        {
            auto spread_start_time_anchor = std::chrono::high_resolution_clock::now();
            init();
            findOverusedRegions();
            for (auto &r : regions) {
                if (merged_regions.count(r.id))
                    continue;
            }
            expandRegions();
            std::queue<std::pair<int, bool>> workqueue;

            for (auto &r : regions) {
                if (merged_regions.count(r.id))
                    continue;
                workqueue.emplace(r.id, false);
            }
            while (!workqueue.empty()) {
                auto front = workqueue.front();
                workqueue.pop();
                auto &r = regions.at(front.first);
                if (std::all_of(r.cells.begin(), r.cells.end(), [](int x) { return x == 0; }))
                    continue;
                auto res = cutRegion(r, front.second);
                if (res) {
                    workqueue.emplace(res->first, !front.second);
                    workqueue.emplace(res->second, !front.second);
                } else {
                    // try the other dir ,in case stuck in one direction only
                    auto res2 = cutRegion(r, !front.second);
                    if (res2) {
                        workqueue.emplace(res2->first, front.second);
                        workqueue.emplace(res2->second, front.second);
                    }
                }
            }
            auto spread_end_time_anchor = std::chrono::high_resolution_clock::now();
            p->spread_time += std::chrono::duration<float>(spread_end_time_anchor - spread_start_time_anchor).count();
        }

      private:
        ForcePlacer *p;
        Context *ctx;
        std::unordered_set<IdString> beltype;
        std::unordered_map<IdString, int> type_index;
        std::vector<std::vector<std::vector<int>>> occupancy;
        std::vector<std::vector<int>> groups;
        std::vector<std::vector<ChainExtent>> chaines;
        std::map<IdString, ChainExtent> cell_extents;

        std::vector<std::vector<std::vector<std::vector<BelId>>> *> fb;

        std::vector<SpreaderRegion> regions;
        std::unordered_set<int> merged_regions;
        // cells at a location. sorted by real (not integer) x and y
        std::vector<std::vector<std::vector<CellInfo *>>> cells_at_location;

        int occ_at(int x, int y, int type) { return occupancy.at(x).at(y).at(type); }
        int bels_at(int x, int y, int type)
        {
            if (fb.at(type) == nullptr || x >= int(fb.at(type)->size()) || y >= int(fb.at(type)->at(x).size()))
                return 0;
            return int(fb.at(type)->at(x).at(y).size());
        }

        void init()
        {
            occupancy.resize(p->max_x + 1,
                             std::vector<std::vector<int>>(p->max_y + 1, std::vector<int>(beltype.size(), 0)));
            groups.resize(p->max_x + 1, std::vector<int>(p->max_y + 1, -1));
            chaines.resize(p->max_x + 1, std::vector<ChainExtent>(p->max_y + 1));
            cells_at_location.resize(p->max_x + 1, std::vector<std::vector<CellInfo *>>(p->max_y + 1));
            for (int x = 0; x <= p->max_x; x++) {
                for (int y = 0; y <= p->max_y; y++) {
                    for (int t = 0; t < int(beltype.size()); t++) {
                        occupancy.at(x).at(y).at(t) = 0;
                    }
                    groups.at(x).at(y) = -1;
                    chaines.at(x).at(y) = {x, y, x, y};
                }
            }
            auto set_chain_ext = [&](IdString cell, int x, int y) {
                if (!cell_extents.count(cell))
                    cell_extents[cell] = {x, y, x, y};
                else {
                    cell_extents[cell].x0 = std::min(cell_extents[cell].x0, x);
                    cell_extents[cell].x1 = std::max(cell_extents[cell].x1, x);
                    cell_extents[cell].y0 = std::min(cell_extents[cell].y0, y);
                    cell_extents[cell].y1 = std::max(cell_extents[cell].y1, y);
                }
            };

            for (auto &cell : p->cell_locs) {
                if (!beltype.count(ctx->cells.at(cell.first)->type))
                    continue;
                if (ctx->cells.at(cell.first)->belStrength > STRENGTH_STRONG)
                    continue;
                occupancy.at(cell.second.x).at(cell.second.y).at(type_index.at(ctx->cells.at(cell.first)->type))++;
                if (p->chain_root.count(cell.first))
                    set_chain_ext(p->chain_root.at(cell.first)->name, cell.second.x, cell.second.y);
                else if (!ctx->cells.at(cell.first)->constr_children.empty())
                    set_chain_ext(cell.first, cell.second.x, cell.second.y);
            }

            for (auto &cell : p->cell_locs) {
                if (!beltype.count(ctx->cells.at(cell.first)->type))
                    continue;
                ChainExtent *ce = nullptr;
                if (p->chain_root.count(cell.first))
                    ce = &(cell_extents.at(p->chain_root.at(cell.first)->name));
                else if (!ctx->cells.at(cell.first)->constr_children.empty())
                    ce = &(cell_extents.at(cell.first));
                if (ce) {
                    auto &lce = chaines.at(cell.second.x).at(cell.second.y);
                    lce.x0 = std::min(lce.x0, ce->x0);
                    lce.y0 = std::min(lce.y0, ce->y0);
                    lce.x1 = std::max(lce.x1, ce->x1);
                    lce.y1 = std::max(lce.y1, ce->y1);
                }
            }
            for (auto cell : p->solve_cells) {
                if (!beltype.count(cell->type))
                    continue;
                cells_at_location.at(p->cell_locs.at(cell->name).x).at(p->cell_locs.at(cell->name).y).push_back(cell);
            }
        }

        void mergeRegions(SpreaderRegion &merged, SpreaderRegion &mergee)
        {
            for (int x = mergee.x0; x <= mergee.x1; x++) {
                for (int y = mergee.y0; y <= mergee.y1; y++) {
                    NPNR_ASSERT(groups.at(x).at(y) == mergee.id);
                    groups.at(x).at(y) = merged.id;
                    for (size_t t = 0; t < beltype.size(); t++) {
                        merged.cells.at(t) += occ_at(x, y, t);
                        merged.bels.at(t) += bels_at(x, y, t);
                    }
                }
            }
            merged_regions.insert(mergee.id);
            growRegion(merged, mergee.x0, mergee.y0, mergee.x1, mergee.y1);
        }

        void growRegion(SpreaderRegion &r, int x0, int y0, int x1, int y1, bool init = false)
        {
            // log_info("growing to (%d, %d) |_> (%d, %d).\n", x0, y0, x1, y1);
            if ((x0 >= r.x0 && y0 >= r.y0 && x1 <= r.x1 && y1 <= r.y1) || init)
                return;
            if (x0 < 0 || x1 > p->max_x || y0 < 0 || y1 > p->max_y)
                return;
            int old_x0 = r.x0 + (init ? 1 : 0), old_y0 = r.y0, old_x1 = r.x1, old_y1 = r.y1;
            r.x0 = std::min(r.x0, x0);
            r.y0 = std::min(r.y0, y0);
            r.x1 = std::max(r.x1, x1);
            r.y1 = std::max(r.y1, y1);

            auto process_location = [&](int x, int y) {
                // merge any overlapping regions
                if (groups.at(x).at(y) == -1) {
                    for (int t = 0; t < int(beltype.size()); t++) {
                        r.bels.at(t) += bels_at(x, y, t);
                        r.cells.at(t) += occ_at(x, y, t);
                    }
                }
                if (groups.at(x).at(y) != -1 && groups.at(x).at(y) != r.id)
                    mergeRegions(r, regions.at(groups.at(x).at(y)));
                groups.at(x).at(y) = r.id;
                auto &chaine = chaines.at(x).at(y);
                growRegion(r, chaine.x0, chaine.y0, chaine.x1, chaine.y1);
            };
            for (int x = r.x0; x < old_x0; x++)
                for (int y = r.y0; y <= r.y1; y++)
                    process_location(x, y);
            for (int x = old_x1 + 1; x <= x1; x++)
                for (int y = r.y0; y <= r.y1; y++)
                    process_location(x, y);
            for (int y = r.y0; y < old_y0; y++)
                for (int x = r.x0; x <= r.x1; x++)
                    process_location(x, y);
            for (int y = old_y1 + 1; y <= r.y1; y++)
                for (int x = r.x0; x <= r.x1; x++)
                    process_location(x, y);
        }

        void findOverusedRegions()
        {
            for (int x = 0; x <= p->max_x; x++) {
                for (int y = 0; y <= p->max_y; y++) {
                    if (groups.at(x).at(y) != -1)
                        continue;
                    bool overutilised = false;
                    for (size_t t = 0; t < beltype.size(); t++) {
                        if (occ_at(x, y, t) > bels_at(x, y, t)) {
                            overutilised = true;
                            break;
                        }
                    }
                    if (!overutilised)
                        continue;

                    int id = int(regions.size());
                    groups.at(x).at(y) = id;
                    SpreaderRegion reg;
                    reg.id = id;
                    reg.x0 = reg.x1 = x;
                    reg.y0 = reg.y1 = y;
                    for (size_t t = 0; t < beltype.size(); t++) {
                        reg.bels.push_back(bels_at(x, y, t));
                        reg.cells.push_back(occ_at(x, y, t));
                    }
                    // make sure we cover carries, etc
                    growRegion(reg, reg.x0, reg.y0, reg.x1, reg.y1, true);

                    bool expanded = true;
                    while (expanded) {
                        expanded = false;
                        // keep trying expansion in x and y, until we find no over-occupancy cells
                        // or hit grouped cells

                        // first trying expanding in x
                        if (reg.x1 < p->max_x) {
                            bool over_occ_x = false;
                            for (int y1 = reg.y0; y1 <= reg.y1; y1++) {
                                for (size_t t = 0; t < beltype.size(); t++) {
                                    if (occ_at(reg.x1 + 1, y1, t) > bels_at(reg.x1 + 1, y1, t)) {
                                        over_occ_x = true;
                                        break;
                                    }
                                }
                            }
                            if (over_occ_x) {
                                expanded = true;
                                growRegion(reg, reg.x0, reg.y0, reg.x1 + 1, reg.y1);
                            }
                        }

                        if (reg.y1 < p->max_y) {
                            bool over_occ_y = false;
                            for (int x1 = reg.x0; x1 <= reg.x1; x1++) {
                                for (size_t t = 0; t < beltype.size(); t++) {
                                    if (occ_at(x1, reg.y1 + 1, t) > bels_at(x1, reg.y1 + 1, t)) {
                                        over_occ_y = true;
                                        break;
                                    }
                                }
                            }
                            if (over_occ_y) {
                                expanded = true;
                                growRegion(reg, reg.x0, reg.y0, reg.x1, reg.y1 + 1);
                            }
                        }
                    }
                    regions.push_back(reg);
                }
            }
        }

        void expandRegions()
        {
            std::queue<int> overu_regions;
            float beta = p->cfg.beta;
            for (auto &r : regions) {
                if (!merged_regions.count(r.id) && r.overused(beta))
                    overu_regions.push(r.id);
            }
            while (!overu_regions.empty()) {
                int rid = overu_regions.front();
                overu_regions.pop();
                if (merged_regions.count(rid))
                    continue;
                auto &reg = regions.at(rid);
                while (reg.overused(beta)) {
                    bool changed = false;
                    for (int j = 0; j < p->cfg.spread_scale_x; j++) {
                        if (reg.x0 > 0) {
                            growRegion(reg, reg.x0 - 1, reg.y0, reg.x1, reg.y1);
                            changed = true;
                            if (!reg.overused(beta))
                                break;
                        }
                        if (reg.x1 < p->max_x) {
                            growRegion(reg, reg.x0, reg.y0, reg.x1 + 1, reg.y1);
                            changed = true;
                            if (!reg.overused(beta))
                                break;
                        }
                    }
                    for (int j = 0; j < p->cfg.spread_scale_y; j++) {
                        if (reg.y0 > 0) {
                            growRegion(reg, reg.x0, reg.y0 - 1, reg.x1, reg.y1);
                            changed = true;
                            if (!reg.overused(beta))
                                break;
                        }
                        if (reg.y1 < p->max_y) {
                            growRegion(reg, reg.x0, reg.y0, reg.x1, reg.y1 + 1);
                            changed = true;
                            if (!reg.overused(beta))
                                break;
                        }
                    }
                    if (!changed) {
                        for (auto bt : sorted(beltype)) {
                            if (reg.cells > reg.bels)
                                log_error("Failed to expand region (%d, %d) |_> (%d, %d) of %d %ss\n", reg.x0, reg.y0,
                                          reg.x1, reg.y1, reg.cells.at(type_index.at(bt)), bt.c_str(ctx));
                        }
                        break;
                    }
                }
            }
        }

        std::vector<CellInfo *> cut_cells;
        boost::optional<std::pair<int, int>> cutRegion(SpreaderRegion &r, bool dir)
        {
            cut_cells.clear();
            auto &cal = cells_at_location;
            int total_cells = 0, total_bels = 0;
            for (int x = r.x0; x <= r.x1; x++) {
                for (int y = r.y0; y <= r.y1; y++) {
                    std::copy(cal.at(x).at(y).begin(), cal.at(x).at(y).end(), std::back_inserter(cut_cells));
                    for (size_t t = 0; t < beltype.size(); t++)
                        total_bels += bels_at(x, y, t);
                }
            }
            for (auto &cell : cut_cells) {
                total_cells += p->chain_size.count(cell->name) ? p->chain_size.at(cell->name) : 1;
            }

            std::sort(cut_cells.begin(), cut_cells.end(), [&](const CellInfo *a, const CellInfo *b) {
                return dir ? (p->cell_locs.at(a->name).rawy < p->cell_locs.at(b->name).rawy)
                           : (p->cell_locs.at(a->name).rawx < p->cell_locs.at(b->name).rawx);
            });

            if (cut_cells.size() < 2)
                return {};
            // find the cells midpoint, counting chains in terms of their total size - making the inital source cut
            int pivot_cells = 0;
            int pivot = 0;
            for (auto &cell : cut_cells) {
                pivot_cells += p->chain_size.count(cell->name) ? p->chain_size.at(cell->name) : 1;
                if (pivot_cells >= total_cells / 2)
                    break;
                pivot++;
            }
            if (pivot >= int(cut_cells.size())) {
                pivot = int(cut_cells.size()) - 1;
            }

            int clearance_l = 0, clearance_r = 0;
            for (size_t i = 0; i < cut_cells.size(); i++) {
                int size;
                if (cell_extents.count(cut_cells.at(i)->name)) {
                    auto &ce = cell_extents.at(cut_cells.at(i)->name);
                    size = dir ? (ce.y1 - ce.y0 + 1) : (ce.x1 - ce.x0 + 1);
                } else {
                    size = 1;
                }
                if (int(i) < pivot) {
                    clearance_l = std::max(clearance_l, size);
                } else {
                    clearance_r = std::max(clearance_r, size);
                }
            }
            // find the target cut that minimises difference in utilisation, whilst trying to ensure that all chains
            // still fit

            // first trim the boundaries of the region in the axis-of-interest, skipping any rows/cols without any bels
            // of the appropriate type
            int trimmed_l = dir ? r.y0 : r.x0, trimmed_r = dir ? r.y1 : r.x1;
            while (trimmed_l < (dir ? r.y1 : r.x1)) {
                bool have_bels = false;
                for (int i = (dir ? r.x0 : r.y0); i <= (dir ? r.x1 : r.y1) && !have_bels; i++) {
                    for (size_t t = 0; t < beltype.size(); t++) {
                        if (bels_at(dir ? i : trimmed_l, dir ? trimmed_l : i, t) > 0) {
                            have_bels = true;
                            break;
                        }
                    }
                }
                if (have_bels)
                    break;
                trimmed_l++;
            }
            while (trimmed_r > (dir ? r.y0 : r.x0)) {
                bool have_bels = false;
                for (int i = (dir ? r.x0 : r.y0); i <= (dir ? r.x1 : r.y1) && !have_bels; i++) {
                    for (size_t t = 0; t < beltype.size(); t++) {
                        if (bels_at(dir ? i : trimmed_r, dir ? trimmed_r : i, t) > 0) {
                            have_bels = true;
                            break;
                        }
                    }
                }
                if (have_bels)
                    break;
                trimmed_r--;
            }

            if ((trimmed_r - trimmed_l + 1) <= std::max(clearance_l, clearance_r))
                return {};
            // Now find the initial target cut that minimises utilisation imbalance, whilst
            // meeting the clearance requirements for any large macros
            std::vector<int> left_cells_v(beltype.size(), 0), right_cells_v(beltype.size(), 0);
            std::vector<int> left_bels_v(beltype.size(), 0), right_bels_v(r.bels);
            for (int i = 0; i <= pivot; i++)
                left_cells_v.at(type_index.at(cut_cells.at(i)->type)) +=
                        p->chain_size.count(cut_cells.at(i)->name) ? p->chain_size.at(cut_cells.at(i)->name) : 1;
            for (int i = pivot + 1; i < int(cut_cells.size()); i++)
                right_cells_v.at(type_index.at(cut_cells.at(i)->type)) +=
                        p->chain_size.count(cut_cells.at(i)->name) ? p->chain_size.at(cut_cells.at(i)->name) : 1;

            int best_tgt_cut = -1;
            double best_detaU = std::numeric_limits<double>::max();

            std::vector<int> silther_bels(beltype.size(), 0);
            for (int i = trimmed_l; i <= trimmed_r; i++) {
                for (size_t t = 0; t < beltype.size(); t++)
                    silther_bels.at(t) = 0;
                for (int j = (dir ? r.x0 : r.y0); j <= (dir ? r.x1 : r.y1); j++) {
                    for (size_t t = 0; t < beltype.size(); t++) {
                        silther_bels.at(t) += dir ? bels_at(j, i, t) : bels_at(i, j, t);
                    }
                }
                for (size_t t = 0; t < beltype.size(); t++) {
                    left_bels_v.at(t) += silther_bels.at(t);
                    right_bels_v.at(t) -= silther_bels.at(t);
                }

                if (((i - trimmed_l) + 1) >= clearance_l && ((trimmed_r - i) + 1) >= clearance_r) {
                    double aU = 0.0;
                    for (size_t t = 0; t < beltype.size(); t++) {
                        aU += (left_cells_v.at(t) + right_cells_v.at(t)) *
                              std::abs(double(left_cells_v.at(t)) / double(std::max(left_bels_v.at(t), 1)) -
                                       double(right_cells_v.at(t)) / double(std::max(right_cells_v.at(t), 1)));
                    }
                    if (aU < best_detaU) {
                        best_detaU = aU;
                        best_tgt_cut = i;
                    }
                }
            }
            if (best_tgt_cut == -1)
                return {};

            for (size_t t = 0; t < beltype.size(); t++) {
                left_bels_v.at(t) = 0;
                right_bels_v.at(t) = 0;
            }
            for (int x = r.x0; x <= (dir ? r.x1 : best_tgt_cut); x++) {
                for (int y = r.y0; y <= (dir ? best_tgt_cut : r.y1); y++) {
                    for (size_t t = 0; t < beltype.size(); t++) {
                        left_bels_v.at(t) += bels_at(x, y, t);
                    }
                }
            }
            for (int x = (dir ? r.x0 : (best_tgt_cut + 1)); x <= r.x1; x++) {
                for (int y = (dir ? (best_tgt_cut + 1) : r.y0); y <= r.y1; y++) {
                    for (size_t t = 0; t < beltype.size(); t++) {
                        right_bels_v.at(t) += bels_at(x, y, t);
                    }
                }
            }
            if (std::accumulate(left_bels_v.begin(), left_bels_v.end(), 0) == 0 ||
                std::accumulate(right_bels_v.begin(), right_bels_v.end(), 0) == 0)
                return {};

            auto is_part_overutil = [&](bool r) {
                double delta = 0;
                for (size_t t = 0; t < left_cells_v.size(); t++) {
                    delta = double(left_cells_v.at(t)) / double(std::max(left_bels_v.at(t), 1)) -
                            double(right_cells_v.at(t)) / double(std::max(right_bels_v.at(t), 1));
                }
                return r ? delta < 0 : delta > 0;
            };

            while (pivot > 0 && is_part_overutil(false)) {
                auto &move_cell = cut_cells.at(pivot);
                int size = p->chain_size.count(move_cell->name) ? p->chain_size.at(move_cell->name) : 1;
                left_cells_v.at(type_index.at(cut_cells.at(pivot)->type)) -= size;
                right_cells_v.at(type_index.at(cut_cells.at(pivot)->type)) += size;
                pivot--;
            }
            while (pivot < int(cut_cells.size()) - 1 && is_part_overutil(true)) {
                auto &move_cell = cut_cells.at(pivot + 1);
                int size = p->chain_size.count(move_cell->name) ? p->chain_size.at(move_cell->name) : 1;
                left_cells_v.at(type_index.at(cut_cells.at(pivot)->type)) += size;
                right_cells_v.at(type_index.at(cut_cells.at(pivot)->type)) -= size;
                pivot++;
            }

            // split regions in bins, and then spread cells by linear interpolation within those bins
            auto spread_binlerp = [&](int cells_start, int cells_end, double area_l, double area_r) {
                int N = cells_end - cells_start;
                if (N <= 2) {
                    for (int i = cells_start; i < cells_end; i++) {
                        auto &pos = dir ? p->cell_locs.at(cut_cells.at(i)->name).rawy
                                        : p->cell_locs.at(cut_cells.at(i)->name).rawx;
                        pos = area_l + i * ((area_r - area_l) / N);
                    }
                    return;
                }
                // split region into up to 10 (K) bins
                int K = std::min<int>(N, 10);
                std::vector<std::pair<int, double>> bin_bounds; // [(cell start, area start)]
                bin_bounds.emplace_back(cells_start, area_l);
                for (int i = 1; i < K; i++)
                    bin_bounds.emplace_back(cells_start + (N * i) / K, area_l + ((area_r - area_l + 0.99) * i) / K);
                bin_bounds.emplace_back(cells_end, area_r + 0.99);
                for (int i = 0; i < K; i++) {
                    auto &bl = bin_bounds.at(i), br = bin_bounds.at(i + 1);
                    double orig_left = dir ? p->cell_locs.at(cut_cells.at(bl.first)->name).rawy
                                           : p->cell_locs.at(cut_cells.at(bl.first)->name).rawx;
                    double orig_right = dir ? p->cell_locs.at(cut_cells.at(br.first - 1)->name).rawy
                                            : p->cell_locs.at(cut_cells.at(br.first - 1)->name).rawx;
                    double m = (br.second - bl.second) / std::max(0.00001, orig_right - orig_left);
                    for (int j = bl.first; j < br.first; j++) {
                        Region *cr = cut_cells.at(j)->region;
                        if (cr != nullptr) {
                            // limit spreading bounds to constraint region; if applicable
                            double brsc = p->limit_to_reg(cr, br.second, dir);
                            double blsc = p->limit_to_reg(cr, bl.second, dir);
                            double mr = (brsc - blsc) / std::max(0.00001, orig_right - orig_left);
                            auto &pos = dir ? p->cell_locs.at(cut_cells.at(j)->name).rawy
                                            : p->cell_locs.at(cut_cells.at(j)->name).rawx;
                            NPNR_ASSERT(pos >= orig_left && pos <= orig_right);
                            pos = blsc + mr * (pos - orig_left);
                        } else {
                            auto &pos = dir ? p->cell_locs.at(cut_cells.at(j)->name).rawy
                                            : p->cell_locs.at(cut_cells.at(j)->name).rawx;
                            NPNR_ASSERT(pos >= orig_left && pos <= orig_right);
                            pos = bl.second + m * (pos - orig_left);
                        }
                    }
                }
            };
            spread_binlerp(0, pivot + 1, trimmed_l, best_tgt_cut);
            spread_binlerp(pivot + 1, int(cut_cells.size()), best_tgt_cut + 1, trimmed_r);
            // update various data structures
            for (int x = r.x0; x <= r.x1; x++) {
                for (int y = r.y0; y <= r.y1; y++) {
                    cells_at_location.at(x).at(y).clear();
                }
            }
            for (auto cell : cut_cells) {
                auto &cl = p->cell_locs.at(cell->name);
                cl.x = std::min(r.x1, std::max(r.x0, int(cl.rawx)));
                cl.y = std::min(r.y1, std::max(r.y0, int(cl.rawy)));
                cells_at_location.at(cl.x).at(cl.y).push_back(cell);
            }
            SpreaderRegion rl, rr;
            rl.id = int(regions.size());
            rl.x0 = r.x0;
            rl.y0 = r.y0;
            rl.x1 = dir ? r.x1 : best_tgt_cut;
            rl.y1 = dir ? best_tgt_cut : r.y1;
            rl.cells = left_cells_v;
            rl.bels = left_bels_v;
            rr.id = int(regions.size()) + 1;
            rr.x0 = dir ? r.x0 : (best_tgt_cut + 1);
            rr.y0 = dir ? (best_tgt_cut + 1) : r.y0;
            rr.x1 = r.x1;
            rr.y1 = r.y1;
            rr.cells = right_cells_v;
            rr.bels = right_bels_v;
            regions.push_back(rl);
            regions.push_back(rr);
            for (int x = rl.x0; x <= rl.x1; x++) {
                for (int y = rl.y0; y <= rl.y1; y++) {
                    groups.at(x).at(y) = rl.id;
                }
            }
            for (int x = rr.x0; x <= rr.x1; x++) {
                for (int y = rr.y0; y <= rr.y1; y++) {
                    groups.at(x).at(y) = rr.id;
                }
            }
            return std::make_pair(rl.id, rr.id);
        }
    };
};

PlacerFCfg::PlacerFCfg(Context *ctx)
{
    hpwl_scale_x = 1;
    hpwl_scale_y = 1;
    spread_scale_x = 1;
    spread_scale_y = 1;
    phi = 1;
    gamma = 1;
    criticalityExponent = ctx->setting<int>("placerForce/criticalityExponent", 2);
    timingWeight = ctx->setting<int>("placerForce/timingWeight", 10);
    beta = ctx->setting<float>("placerForce/beta", 0.9);
    alpha = ctx->setting<float>("placerForce/alpha", 0.1);
    timeDriven = true;
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