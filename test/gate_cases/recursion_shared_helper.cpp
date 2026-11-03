// GATE: SAFE
// A helper reached along several distinct call paths is not a cycle. Also
// pins the memo in the call-graph walk: without it, fan-out like this is
// re-explored once per path.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(1)});
double leaf(double x) { return x + 1.0; }
double mid_a(double x) { return leaf(x) + leaf(x); }
double mid_b(double x) { return leaf(x) + mid_a(x); }
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    return mid_a(1.0) + mid_b(2.0);
};
config.set_scoring_fn(scoring_fn);
