// Fast-adapting EWMA with optimized bandwidth scaling
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.77})
});
f_config.add_listeners(f_dram_bw, {
    vulcan::listeners::global::EWMA({0.29})
});
f_config.add_listeners(f_nvm_bw, {
    vulcan::listeners::global::EWMA({0.29})
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double a = fs.get_ewma(f_accesses, obj_id, 0.77);
    double d = fs.get_ewma(f_dram_bw, 0.29);
    double n = fs.get_ewma(f_nvm_bw, 0.29);
    
    // Bandwidth-aware multiplier
    double r = (n > 0.01) ? (d / n) : 1.0;
    double m = 1.0 + 0.11 * (r - 1.0);
    m = (m < 0.57) ? 0.57 : (m > 1.85) ? 1.85 : m;
    
    return a * m;
};