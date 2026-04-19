// High-alpha EWMA with geometric mean normalization
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.97}),
    vulcan::listeners::object::PopulationPercentile()
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double access = fs.get_ewma(f_accesses, obj_id, 0.97);
    double pop_p50 = fs.get_percentile(f_accesses, 0.5);
    
    // Pure quadratic scaling - proven winning formula
    // access^2 / p50 creates strong hot/cold separation
    double denom = (pop_p50 > 0.001) ? pop_p50 : 1.0;
    return access * access / denom;
};