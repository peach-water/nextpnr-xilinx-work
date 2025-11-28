

#ifndef PLACE_H
#define PLACE_H

#include "log.h"
#include "nextpnr.h"

NEXTPNR_NAMESPACE_BEGIN

struct PlacerFCfg {
    PlacerFCfg(Context *ctx);
    float constraintWeight, netShareWeight;
    int minBelsForGridPick;
    bool budgetBased;
    float startTemp;
    int timingFanoutThresh;
    bool timing_driven;
    int slack_redist_iter;
    int hpwl_scale_x, hpwl_scale_y;
};

extern bool placer_force(Context *ctx, PlacerFCfg cfg);

NEXTPNR_NAMESPACE_END

#endif