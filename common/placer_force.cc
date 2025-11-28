

#include "placer_force.h"
#include <algorithm>
#include <chrono>
#include <map>
#include <string>
#include <vector>
#include "place_common.h"
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
    void place()
    {
        log_break();
        ctx->lock();

        size_t placed_cells = 0;
        std::vector<CellInfo *> autoplaced;
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
                placed_cells++;
                locked_bels.insert(bel);
            }
        }
        int constr_placed_cells = placed_cells;
        log_info("Placed %d cells based on constraints.\n", placed_cells);
        ctx->yield();

        // 初始化未放置的CELL的位置
        // 找出所有未放置的cell对象
        for (auto &cell : ctx->cells) {
            CellInfo *ci = cell.second.get();
            if (ci->bel == BelId()) {
                autoplaced.push_back(cell.second.get());
            }
        }
        std::sort(autoplaced.begin(), autoplaced.end(), [](CellInfo *a, CellInfo *b) { return a->name < b->name; });
        ctx->shuffle(autoplaced);
        log_info("Creating initial placement for remaining %d cells.\n", int(autoplaced.size()));
        auto place_start_time_anchor_point = std::chrono::high_resolution_clock::now(); // 开始计时锚点
        // 随机初始化放置
        for (auto cell : autoplaced) {
            placeInital(cell);
            placed_cells++;
            if ((placed_cells - constr_placed_cells) % 500 == 0)
                log_info("  initial placement placed %d/%d cells.\n", int(placed_cells - constr_placed_cells));
        }
        if ((placed_cells - constr_placed_cells) % 500 != 0)
            log_info("  initial placement placed %d/%d cells.\n", int(placed_cells - constr_placed_cells),
                     int(autoplaced.size()));
        // 暂时不确定用途，应该是计算时序约束
        if (cfg.budgetBased && cfg.slack_redist_iter > 0)
            assign_budget(ctx);

        ctx->yield();
        auto place_end_time_anchor_point = std::chrono::high_resolution_clock::now(); // 结束计时锚点
        log_info("Initial placement time %.2fs\n",
                 std::chrono::duration<float>(place_end_time_anchor_point - place_start_time_anchor_point).count());
        log_info("Runing Force placer.\n");
        // placer初始化结束

        // placer正式算法开始
        place_start_time_anchor_point = std::chrono::high_resolution_clock::now();
        if (!cfg.budgetBased)
            get_criticalities(ctx, &net_crit);
        
        // 计算初始代价
        setupCost();
        // 移动控制

        // 计算线长开销与延迟开销
        

        place_end_time_anchor_point = std::chrono::high_resolution_clock::now();


        ctx->unlock();
    }

  private:
    // 随机初始化放置
    void placeInital(CellInfo *cell)
    {
        bool all_placed = false;
        int iters = 25; // 尝试25次
        while (!all_placed) {
            BelId best_bel = BelId();
            uint64_t best_score = std::numeric_limits<uint64_t>::max(),
                     best_ripup_score = std::numeric_limits<uint64_t>::max();
            // 无视资源限制的虚拟BEL位置。当物理BEL因为各种原因无法放置时（比如部分资源被占用），会清理掉虚拟BEL上已放置的所有cell，放置当前cell。
            CellInfo *ripup_target = nullptr; // 被驱赶的cell本体
            BelId ripup_bel = BelId();        // 被驱赶的cell占据的bel对象
            if (cell->bel != BelId()) {
                ctx->unbindBel(cell->bel);
            }
            IdString target_type = cell->type;

            auto proc_bel = [&](BelId bel) {
                if (ctx->getBelType(bel) == target_type && ctx->isValidBelForCell(cell, bel)) {
                    if (ctx->checkBelAvail(bel)) {
                        uint64_t score = ctx->rng64();
                        if (score < best_score) {
                            best_score = score;
                            best_bel = bel;
                        }
                    } else {
                        uint64_t score = ctx->rng64();
                        CellInfo *bound_cell = ctx->getBoundBelCell(bel);
                        // 判断绑定强度小于STRENGTH_STRONG，避免驱赶cell时驱赶了约束文件规定的cell
                        if (score <= best_ripup_score && bound_cell->belStrength < STRENGTH_STRONG) {
                            best_ripup_score = score;
                            ripup_target = bound_cell;
                            ripup_bel = bel;
                        }
                    }
                }
            };

            // 如果有区域限制，那就从限制区域的bel尝试，否则从全局遍历的bel尝试
            if (cell->region != nullptr && cell->region->constr_bels) {
                for (auto bel : cell->region->bels) {
                    proc_bel(bel);
                }
            } else {
                for (auto bel : ctx->getBels()) {
                    proc_bel(bel);
                }
            }

            // 当初始化放置失败时
            if (best_bel == BelId()) {
                if (iters == 0 || ripup_bel == BelId())
                    log_error("failed to initlize place cell \'%s\' of type \'%s\'.\n", cell->name.c_str(ctx),
                              cell->type.c_str(ctx));
                --iters;
                // 鸠占鹊巢
                ctx->unbindBel(ripup_target->bel);
                best_bel = ripup_bel;
            } else {
                all_placed = true;
            }
            ctx->bindBel(best_bel, cell, STRENGTH_WEAK);

            cell->attrs[ctx->id("BEL")] = ctx->getBelName(cell->bel).str(ctx);
            cell = ripup_target; // 现在开始处理被驱赶的对象
        }
    }

    // 初始化代价 map
    void setupCost() {
        for (auto net : sorted(ctx->nets)) {
            NetInfo *ni = net.second;
            if (ignoreNet(ni)) // 不需要关心的net
                continue;
            net_bounds[ni->udata] = getNetBounds(ni);
            if (cfg.timing_driven && int(ni->users.size()) < cfg.timingFanoutThresh)
                for (size_t i = 0; i < ni->users.size(); i++) 
                    net_arc_tcost[ni->udata][i] = getTimingCost(ni, i);
        }
    }

    // 计算net中到特定端口的延迟
    inline double getTimingCost(NetInfo* net, size_t user) {
        int cc;
        if (net->driver.cell == nullptr)
            return 0;
        if (ctx->getPortTimingClass(net->driver.cell, net->driver.port, cc) == TMG_IGNORE)
            return 0;
        if (cfg.budgetBased) {
            double delay = ctx->getDelayNS(ctx->predictDelay(net, net->users.at(user)));
            return std::min(10.0, std::exp(delay - ctx->getDelayNS(net->users.at(user).budget)/10));
        }
        auto crit = net_crit.find(net->name); // 找到延迟惩罚项
        if (crit == net_crit.end() || crit->second.criticality.empty())
            return 0;
        double delay = ctx->getDelayNS(ctx->predictDelay(net, net->users.at(user)));
        return delay * std::pow(crit->second.criticality.at(user), crit_exp);
    }

    // 计算net的最小包围盒
    inline BoundingBox getNetBounds(NetInfo* net){
        BoundingBox bb;
        NPNR_ASSERT(net->driver.cell != nullptr);
        Loc dloc = ctx->getBelLocation(net->driver.cell->bel);
        bb.x0, bb.x1 = dloc.x, dloc.x;
        bb.y0, bb.y1 = dloc.y, dloc.y;
        bb.nx0, bb.nx1, bb.ny0, bb.ny1 = 1,1,1,1;
        for (auto user : net->users) {
            if (user.cell->bel == BelId())
                continue;
            Loc uloc = ctx->getBelLocation(user.cell->bel);
            if (uloc.x == bb.x0)
                bb.nx0 ++;
            else if (uloc.x < bb.x0){
                bb.x0 = uloc.x;
                bb.nx0 = 1;
            }
            if (uloc.x == bb.x1)
                bb.nx1 ++;
            else if (uloc.x > bb.x1) {
                bb.x1 = uloc.x;
                bb.nx1 = 1;
            }
            if (uloc.y == bb.y0)
                bb.ny0 ++;
            else if (uloc.y < bb.y0) {
                bb.y0 = uloc.y;
                bb.ny0 = 1;
            }
            if (uloc.y == bb.y1)
                bb.ny1 ++;
            else if (uloc.y > bb.y1) {
                bb.y1 = uloc.y;
                bb.ny1 = 1;
            }
        }
        return bb;
    }

    // 判断net是否有记录代价的必要，比如没有驱动port的net就没有意义
    inline bool ignoreNet(NetInfo *net) {
        return net->driver.cell == nullptr || net->driver.cell->bel == BelId() || ctx->getBelGlobalBuf(net->driver.cell->bel);
    }

    // 计算总线长开销
    wirelen_t totalWirelenCost() {
        wirelen_t cost = 0;
        for (const auto &net : net_bounds)
            cost += net.hpwl(cfg);
        return cost;
    }

    // 计算延迟开销
    double totalTimingCost() {
        double cost = 0.0f;
        for (const auto &net : net_arc_tcost) {
            for (auto arc_cost : net) {
                cost += arc_cost;
            }
        }
        return cost;
    }

    // 基本信息
    Context *ctx;
    PlacerFCfg cfg;
    float crit_exp = 8.0f;

    int diameter = 35, max_x = 1, max_y = 1; // diameter 控制交换空间范围，不确定是否有必要保留
    // 部分网络限制其边界框大小，从而跳过移动到边界框外的无效步骤
    std::vector<BoundingBox> net_bounds;
    // 部分现网的时钟惩罚（criticality * delay ns）
    std::vector<std::vector<double>> net_arc_tcost;
    std::unordered_map<IdString, std::tuple<int, int>> bel_types;
    std::unordered_map<IdString, BoundingBox> region_bounds;

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