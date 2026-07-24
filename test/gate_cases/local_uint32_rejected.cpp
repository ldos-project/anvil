// GATE: UNSAFE
// Anvil has no uint32_t; it must not slip through as a record type.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    uint32_t x = 5;
    return 1.0;
};
config.set_scoring_fn(scoring_fn);
