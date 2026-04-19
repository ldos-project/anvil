// Track access patterns with multiple listeners for richer information
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.5}),  // Proven alpha value from best performer
    vulcan::listeners::object::RollingWindow(8),  // Optimal window size
    vulcan::listeners::object::PopulationPercentile()  // Better for relative positioning
});

// Track bandwidth to understand tier performance gap
f_config.add_listeners(f_dram_bw, { vulcan::listeners::global::EWMA({0.3}) });
f_config.add_listeners(f_nvm_bw, { vulcan::listeners::global::EWMA({0.3}) });

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    // Get EWMA of accesses - captures recency-weighted access frequency
    double ewma_accesses = fs.get_ewma(f_accesses, obj_id, 0.5);
    
    // Get rolling average for stability
    double rolling_avg = fs.get_avg(f_accesses, obj_id);
    
    // Combine EWMA and rolling average - EWMA dominant for reactivity
    double combined_accesses = 0.72 * ewma_accesses + 0.28 * rolling_avg;
    
    // Get bandwidth ratio to scale importance
    double dram_bw = fs.get_ewma(f_dram_bw, 0.3);
    double nvm_bw = fs.get_ewma(f_nvm_bw, 0.3);
    
    // Higher bandwidth ratio means bigger benefit from promotion
    double bw_ratio = (nvm_bw > 0.1) ? (dram_bw / nvm_bw) : 1.0;
    bw_ratio = std::min(bw_ratio, 10.0);  // Cleaner clamping
    
    // Scale score by log of bandwidth ratio - diminishing returns
    double bw_factor = 1.0 + 0.2 * std::log(bw_ratio + 1.0);
    
    // Final score: higher accesses = higher priority for fast tier
    return combined_accesses * bw_factor;
};