// EVOLVE-BLOCK-START

/*
    Adding all listeners here to test.
*/

config.add_listeners(varG, {
    vulcan::listeners::global::Average(),
    vulcan::listeners::global::MinMax(),
    vulcan::listeners::global::RollingWindow(10),
    vulcan::listeners::global::RollingPercentile(100),
    vulcan::listeners::global::EWMA({0.5, 0.3})
});
config.add_listeners(varO, {
    vulcan::listeners::object::Average(),
    vulcan::listeners::object::MinMax(),
    vulcan::listeners::object::RollingWindow(10),
    vulcan::listeners::object::RollingPercentile(100),
    vulcan::listeners::object::EWMA({0.5, 0.3}),
    vulcan::listeners::object::PopulationPercentile()
});

SCORING_FN(const vulcan::feature_store& fs, int64_t obj_id) {
    // global listener APIs
    double g_avg = fs.get_avg(varG);
    double g_max = fs.get_max(varG);
    double g_min = fs.get_min(varG);
    double g_latest = fs.get_latest(varG);
    double g_kth = fs.get_kth_recent(varG, 2);
    double g_p50 = fs.get_percentile(varG, 0.5);
    double g_ewma1 = fs.get_ewma(varG, 0.5);
    double g_ewma2 = fs.get_ewma(varG, 0.3);

    // object listener APIs
    double o_avg = fs.get_avg(varO, obj_id);
    double o_max = fs.get_max(varO, obj_id);
    double o_min = fs.get_min(varO, obj_id);
    double o_latest = fs.get_latest(varO, obj_id);
    double o_kth = fs.get_kth_recent(varO, obj_id, 2);
    double o_p50 = fs.get_percentile(varO, obj_id, 0.5);
    double o_ewma1 = fs.get_ewma(varO, obj_id, 0.5);
    double o_ewma2 = fs.get_ewma(varO, obj_id, 0.3);
    double o_pop_p50 = fs.get_percentile(varO, 0.5);

    double score = 3;
    for(int i=0; i < 10; i++) score += i;
    
    score = score + g_avg + g_max + g_min + g_latest + g_kth + g_p50
        + g_ewma1 + g_ewma2
        + o_avg + o_max + o_min + o_latest + o_kth + o_p50
        + o_ewma1 + o_ewma2 + o_pop_p50;

    return score;
};
// EVOLVE-BLOCK-END
