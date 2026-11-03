// GATE: UNSAFE
// while carries no syntactic termination argument, even when it terminates.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    int i = 0;
    while (i < 4) { s = s + 1.0; i = i + 1; }
    return s;
};
config.set_scoring_fn(scoring_fn);
