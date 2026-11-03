// GATE: UNSAFE
// Regression: self-recursion once passed the gate.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
double rec(double x) { if (x <= 0.0) { return 0.0; } return rec(x - 1.0); }
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    return rec(static_cast<double>(fs.get_latest(f_count, obj_id)));
};
config.set_scoring_fn(scoring_fn);
