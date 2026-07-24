// GATE: UNSAFE
// Trips only 8 times but still wraps: a trip cap alone is not enough.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    for (int i = 2147483640; i <= 2147483647; i++) { s = s + 1.0; }
    return s;
};
config.set_scoring_fn(scoring_fn);
