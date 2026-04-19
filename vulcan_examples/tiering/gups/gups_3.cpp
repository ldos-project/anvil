// α=0.95/0.345: exploring narrow region between top (0.35) and next tier (0.36)
// Hypothesis: optimal alpha gap is in this tight window
f_config.add_listeners(f_accesses, { 
    vulcan::listeners::object::EWMA({0.95, 0.345})
});

auto scoring_fn = [](const vulcan::feature_store& fs, int64_t obj_id) -> double {
    double fast = fs.get_ewma(f_accesses, obj_id, 0.95);
    double slow = fs.get_ewma(f_accesses, obj_id, 0.345);
    double accel = (slow > 0.001) ? (fast / slow) : 1.0;
    
    // Testing 0.56 multiplier: between top's 0.55 and second-tier 0.57
    return fast * (1.0 + 0.56 * std::min(accel, 2.5));
};