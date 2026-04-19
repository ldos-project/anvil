// Dual-scale EWMA: 0.86 (~2.8 step half-life) for bursts, 0.24 (~8.5 step) for sustained
f_config.add_listeners(f_accesses, {
    vulcan::listeners::object::EWMA({0.86, 0.24}),
    vulcan::listeners::object::PopulationPercentile()
});

f_config.add_listeners(f_dram_bw, {vulcan::listeners::global::EWMA({0.5})});
f_config.add_listeners(f_nvm_bw, {vulcan::listeners::global::EWMA({0.5})});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double fast = fs.get_ewma(f_accesses, obj_id, 0.86);  // Recent bursts
    double slow = fs.get_ewma(f_accesses, obj_id, 0.24);  // Sustained baseline
    
    // 73/27 blend: aggressive recency for insert-heavy latest distribution
    double combined = 0.73 * fast + 0.27 * slow;
    
    // Normalize by p50 for relative comparison
    double p50 = fs.get_percentile(f_accesses, 0.5);  // p50: normalization anchor
    double normalized = combined / (p50 + 0.001);  // +0.001: guards div-by-zero
    
    // Bandwidth ratio: DRAM value relative to NVM
    double nvm_bw = fs.get_ewma(f_nvm_bw, 0.5);
    double bw_factor = (nvm_bw > 0.0) ? std::sqrt(fs.get_ewma(f_dram_bw, 0.5) / nvm_bw) : 1.0;
    
    return normalized * bw_factor;
};