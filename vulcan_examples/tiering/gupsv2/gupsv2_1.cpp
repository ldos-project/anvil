// Source hash: a81ba88ead924ece71467e79a2222d5dac791f08b0526f7f0639946decc49316
// Trend-aware EWMA with bounded trend amplification
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.1, 0.5}),  // alpha=0.1: half-life ~7 steps; alpha=0.5: half-life ~1 step
    vulcan::listeners::object::PopulationPercentile()
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double fast = fs.get_ewma(f_accesses, obj_id, 0.5);  // recent activity
    double slow = fs.get_ewma(f_accesses, obj_id, 0.1);  // long-term baseline
    
    double p50 = fs.get_percentile(f_accesses, 0.5);  // p50: population median anchor
    double norm = (p50 > 0.0) ? p50 : 1.0;
    
    // Trend: ratio capped at 4x to prevent outlier explosion
    double ratio = (slow > 0.0) ? (fast / slow) : 1.0;
    double trend = (ratio < 4.0) ? ratio : 4.0;  // 4x cap: prevents extreme amplification
    return (fast * trend) / norm;
};