// GATE: UNSAFE
// A typo'd or invented type name must fail at the gate, not in g++.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    Frobnicator x = 5;
    return 1.0;
};
config.set_scoring_fn(scoring_fn);
