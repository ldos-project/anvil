// adad5de4480726f19c2ba6f3e1d221147bce01a6288b83
// Simplified: dual-timescale EWMA for PageRank iteration tracking
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.3, 0.7}),  // 0.3: ~7 step half-life, 0.7: ~2 step half-life
    vulcan::listeners::object::PopulationPercentile()
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double fast = fs.get_ewma(f_accesses, obj_id, 0.7);  // Recent
    double slow = fs.get_ewma(f_accesses, obj_id, 0.3);  // Sustained
    
    // p75 normalization to emphasize truly hot pages
    double p75 = fs.get_percentile(f_accesses, 0.75);  // p75: upper quartile anchor
    double norm = (p75 > 0.0) ? p75 : 1.0;
    
    // Combined score: balanced for iterative workload phases
    double base = (0.6 * fast + 0.4 * slow) / norm;  // 0.6/0.4: balance recent activity with sustained access
    
    // Trend boost for heating pages
    double trend = (slow > 0.0) ? std::min(fast / slow, 2.5) : 1.0;  // 2.5: cap outliers
    
    return base * (0.5 + 0.5 * trend);  // 0.5/0.5: equal weight allows trend to double score for hot pages
};