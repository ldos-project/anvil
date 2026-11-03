// GATE: UNSAFE
// new[] stays rejected.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    s = 0.0;
    return s;
};
config.set_scoring_fn(scoring_fn);

double leak() { return new double[10]; }
