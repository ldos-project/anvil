// 9f74aa75ae9aaa55513d5f3d01b042c04943868583e307
// For PageRank: capture both recency and sustained access patterns
// Graph hubs get accessed repeatedly; use EWMA to track this
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.5}),  // 0.5: balanced decay, ~3 samples half-life
    vulcan::listeners::object::PopulationPercentile()
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    // Get smoothed access rate for this page
    double access_rate = fs.get_ewma(f_accesses, obj_id, 0.5);
    
    // Normalize by population median to handle varying scales
    double p50 = fs.get_percentile(f_accesses, 0.5);  // p50: median baseline
    
    // Protect against edge cases
    if (p50 < 0.001) return access_rate;  // 0.001: epsilon for near-zero median
    
    // Score: how much hotter than median (power-law distribution in PageRank)
    return access_rate / p50;
};