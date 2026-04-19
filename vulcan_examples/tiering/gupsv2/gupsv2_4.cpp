// 87a138c59d2fa80c8149ede88367334c1f1556820dc603
// Very fast EWMA (alpha=0.85): rapid adaptation, ~5 samples to forget 50% weight
// Slow EWMA (alpha=0.25): stable baseline, ~9 samples to forget 50%
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.85, 0.25}),
    vulcan::listeners::object::PopulationPercentile()
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    // Fast EWMA to catch hotset shifts quickly
    double fast_ewma = fs.get_ewma(f_accesses, obj_id, 0.85);
    // Slow EWMA for stable baseline
    double slow_ewma = fs.get_ewma(f_accesses, obj_id, 0.25);
    
    // Use p50 and p90 to define hot range
    double p50 = fs.get_percentile(f_accesses, 0.5); // p50: cold/hot boundary
    double p90 = fs.get_percentile(f_accesses, 0.9); // p90: clearly hot threshold
    
    // Range-based normalization: more robust than single percentile
    double range = (p90 > p50) ? (p90 - p50) : 1.0; // avoid division by zero
    
    // Relative hotness: how far above median is this page
    double relative_hotness = (fast_ewma - p50) / range;
    
    // Momentum: detects heating/cooling trends
    double momentum = fast_ewma - slow_ewma;
    double normalized_momentum = momentum / (p50 + 1.0); // +1.0: avoid division by zero
    
    // Combined score: current state + trend with 0.4 weight on momentum
    // 0.4: slightly less emphasis on trend than Program 1, for faster hotset adaptation
    return relative_hotness + 0.4 * normalized_momentum;
};