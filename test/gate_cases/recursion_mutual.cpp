// GATE: UNSAFE
// A cycle through two functions, which no single-function check would see.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
double ping(double x) { return pong(x - 1.0); }
double pong(double x) { return ping(x - 1.0); }
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    return ping(static_cast<double>(fs.get_latest(f_count, obj_id)));
};
config.set_scoring_fn(scoring_fn);
