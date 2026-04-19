// Adaptive scoring with multi-tier hotness classification
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.72}),
    vulcan::listeners::object::PopulationPercentile()
});
f_config.add_listeners(f_dram_bw, {
    vulcan::listeners::global::EWMA({0.25})
});
f_config.add_listeners(f_nvm_bw, {
    vulcan::listeners::global::EWMA({0.25})
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double ewma = fs.get_ewma(f_accesses, obj_id, 0.72);
    double p60 = fs.get_percentile(f_accesses, 0.6);
    double p80 = fs.get_percentile(f_accesses, 0.8);
    double dram_bw = fs.get_ewma(f_dram_bw, 0.25);
    double nvm_bw = fs.get_ewma(f_nvm_bw, 0.25);
    
    double bw_ratio = (nvm_bw > 0.01) ? (dram_bw / nvm_bw) : 1.0;
    double score = ewma;
    
    // Multi-tier amplification: stronger boost for top 20%
    if (p60 > 0.01) {
        double hotness = ewma / p60;
        if (p80 > 0.01 && ewma > p80) {
            // Top 20%: extra aggressive amplification
            score = ewma * (0.4 + 0.6 * hotness);
        } else {
            // Standard amplification for middle tier
            score = ewma * (0.45 + 0.55 * hotness);
        }
    }
    
    // Under bandwidth pressure, increase differentiation
    if (bw_ratio > 1.5) {
        score = std::pow(score + 1.0, 1.15) - 1.0;
    }
    
    return score;
};