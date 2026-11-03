// GATE: UNSAFE
// Regression: i = i + 0 never advances.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    for (int i = 0; i < 4; i = i + 0) { s = s + 1.0; }
    return s;
};
config.set_scoring_fn(scoring_fn);
