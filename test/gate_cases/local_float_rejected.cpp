// GATE: UNSAFE
// The DSL documents no float.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    float x = 5.0;
    return 1.0;
};
config.set_scoring_fn(scoring_fn);
