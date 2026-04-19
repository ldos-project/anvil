// Fast EWMA (alpha=0.8): adapts quickly, ~4 samples to halve old weight
// Slow EWMA (alpha=0.3): more stable baseline, ~7 samples to halve
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.8, 0.3}),
    vulcan::listeners::object::PopulationPercentile()
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    // Fast-adapting EWMA captures recent hotness
    double fast_ewma = fs.get_ewma(f_accesses, obj_id, 0.8);
    // Slower EWMA for baseline comparison
    double slow_ewma = fs.get_ewma(f_accesses, obj_id, 0.3);
    
    // Population median as normalization anchor
    double pop_median = fs.get_percentile(f_accesses, 0.5); // p50: normalization anchor
    double pop_p90 = fs.get_percentile(f_accesses, 0.9);    // p90: hot threshold
    
    // Avoid division by zero
    double normalizer = (pop_p90 > pop_median) ? (pop_p90 - pop_median) : 1.0;
    
    // Normalized current hotness relative to population
    double relative_hotness = (fast_ewma - pop_median) / normalizer;
    
    // Momentum: positive when page is getting hotter, negative when cooling
    // Helps quickly promote newly-hot pages and demote cooling pages
    double momentum = fast_ewma - slow_ewma;
    double normalized_momentum = momentum / (pop_median + 1.0);
    
    // Combined score: base hotness + momentum bonus for trend detection
    // The 0.5 weight on momentum balances stability vs adaptivity
    double score = relative_hotness + 0.5 * normalized_momentum; // 0.5: equal weight to current state and trend
    
    return score;
};