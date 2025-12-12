

#ifndef PLACE_FORCE_H
#define PLACE_FORCE_H

#include "log.h"
#include "nextpnr.h"

NEXTPNR_NAMESPACE_BEGIN

struct PlacerFCfg
{
    PlacerFCfg(Context *ctx);
    float constraintWeight, netShareWeight;
    bool timeDriven;
    int slack_redist_iter;
    int hpwl_scale_x, hpwl_scale_y;
    int spread_scale_x, spread_scale_y;
    int criticalityExponent;
    float timingWeight;

    std::unordered_set<IdString> ioBufTypes;
    std::vector<std::unordered_set<IdString>> cellGroups;
    double phi, gamma; // star算法计算S的参数
    float beta;        // 扩散算法计算阈值
    float alpha;       // 伪连接力权重，越大则伪连接力生效速度越快
};

extern bool placer_force(Context *ctx, PlacerFCfg cfg);

NEXTPNR_NAMESPACE_END

#endif