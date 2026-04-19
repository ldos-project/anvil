// f8081b0b149d9e9830e4de00e6b344c1e02210e7cbf11a
// Track accesses at timescales suited for PageRank's iterative convergence
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.3, 0.7}),  // α=0.3: ~3 steps, α=0.7: ~1.4 steps
    vulcan::listeners::object::PopulationPercentile()
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double recent = fs.get_ewma(f_accesses, obj_id, 0.7);  // Recent activity
    double stable = fs.get_ewma(f_accesses, obj_id, 0.3);  // Sustained pattern
    
    // Blend: 55/45 favoring recent for PageRank's iterative nature
    // Slightly more weight to stability for graph convergence patterns
    double blended = 0.55 * recent + 0.45 * stable;
    
    // Population percentiles for robust normalization
    double p50 = fs.get_percentile(f_accesses, 0.5);  // p50: median anchor
    double p75 = fs.get_percentile(f_accesses, 0.75); // p75: upper quartile threshold
    
    // Normalize using interquartile spread for stability
    double spread = p75 - p50;
    if (spread > 0.0) {
        // Center around median, scale by quartile spread
        double normalized = (blended - p50) / spread;
        // Smooth sigmoid-like transformation for better hot/cold discrimination
        // tanh approximation: x / (1 + |x|/3) gives smooth S-curve
        double scaled = normalized / (1.0 + std::abs(normalized) / 3.0);
        return 1.0 + scaled;  // Offset to keep scores positive
    }
    return (p50 > 0.0) ? blended / p50 : blended;
};