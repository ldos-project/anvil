// GATE: UNSAFE
// Endpoints past 2^53 are where a double counter can no longer represent i+1.
config.add_listeners(f_count, {vulcan::listeners::object::RollingWindow(4)});
auto scoring_fn = [&](FS_REF fs, int64_t obj_id) -> double {
    double s = 0.0;
    for (double i = 9007199254740992; i < 9007199254740996; i++) { s = s + 1.0; }
    return s;
};
config.set_scoring_fn(scoring_fn);
