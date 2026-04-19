// Track accesses with multiple EWMA rates and population-wide comparison
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.3, 0.7}),  // 0.3: slower adaptation (~3 half-life), 0.7: fast adaptation for recency
    vulcan::listeners::object::PopulationPercentile()
});

// Track bandwidth for tier-aware scoring
f_config.add_listeners(f_dram_bw, { vulcan::listeners::global::EWMA({0.2}) });
f_config.add_listeners(f_nvm_bw, { vulcan::listeners::global::EWMA({0.2}) });

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    // Get EWMA at two rates: slow (0.3) captures baseline, fast (0.7) captures recent bursts
    double ewma_slow = fs.get_ewma(f_accesses, obj_id, 0.3);
    double ewma_fast = fs.get_ewma(f_accesses, obj_id, 0.7);
    
    // Combine: weight recent activity more for insert-heavy workload
    // 0.7 weight on fast EWMA emphasizes recency (latest distribution)
    double combined_access = 0.3 * ewma_slow + 0.7 * ewma_fast;
    
    // Trend detection: positive when page is heating up
    double trend = ewma_fast - ewma_slow;
    
    // Get population median (p50) as normalization anchor
    double p50 = fs.get_percentile(f_accesses, 0.5);
    double norm = (p50 > 0.0) ? p50 : 1.0;
    
    // Bandwidth ratio: how much faster is DRAM? Higher ratio = more benefit from promotion
    double dram = fs.get_ewma(f_dram_bw, 0.2);
    double nvm = fs.get_ewma(f_nvm_bw, 0.2);
    double bw_factor = (nvm > 0.0) ? (dram / nvm) : 2.0;  // default 2x if unavailable
    
    // Final score: normalized access rate + trend bonus, scaled by bandwidth benefit
    // Trend adds up to 50% boost for rapidly heating pages
    double base_score = combined_access / norm;
    double trend_bonus = (trend > 0.0) ? 0.5 * (trend / norm) : 0.0;
    
    return (base_score + trend_bonus) * bw_factor;
};