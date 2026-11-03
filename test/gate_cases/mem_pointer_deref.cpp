// GATE: UNSAFE
// Pointers stay rejected.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    int x = 5;
    int* p = &x;
    s = static_cast<double>(*p);
    return s;
};
config.set_scoring_fn(scoring_fn);
