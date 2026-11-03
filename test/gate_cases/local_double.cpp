// GATE: SAFE
// double is the workhorse local type.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double x = 5.0;
    return 1.0;
};
config.set_scoring_fn(scoring_fn);
