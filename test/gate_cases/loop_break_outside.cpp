// GATE: UNSAFE
// break outside a loop is not valid C++, so the gate must not pass it on.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    break;
    return s;
};
config.set_scoring_fn(scoring_fn);
