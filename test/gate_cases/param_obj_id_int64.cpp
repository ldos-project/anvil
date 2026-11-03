// GATE: SAFE
// int64_t on the score function parameter stays legal.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double d = static_cast<double>(fs.get_latest(f_count, obj_id));
    return d;
};
config.set_scoring_fn(scoring_fn);
