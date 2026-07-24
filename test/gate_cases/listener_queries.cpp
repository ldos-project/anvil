// GATE: SAFE
// Listener externs are not recursion candidates.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    s = static_cast<double>(fs.get_latest(f_count, obj_id));
    s = s + fs.get_ewma(f_count, obj_id);
    return s;
};
config.set_scoring_fn(scoring_fn);
