// GATE: UNSAFE
// Same for continue, including inside an if that is not in a loop.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    if (fs.get_latest(f_count, obj_id) > 0) { continue; }
    return 1.0;
};
config.set_scoring_fn(scoring_fn);
