// EVOLVE-BLOCK-START

double values[10]; // illegal

config.add_listeners(varG, {
    vulcan::listeners::global::Average(),
    vulcan::listeners::global::MinMax(),
    vulcan::listeners::global::RollingWindow(10)
});
config.add_listeners(varO, {
    vulcan::listeners::object::Average(),
    vulcan::listeners::object::MinMax(),
    vulcan::listeners::object::RollingWindow(10)
});

SCORING_FN(const vulcan::feature_store& fs, int64_t obj_id) {
    values[obj_id] = fs.get_latest(varG); // no error because our template uses only two objects
    return *values; // illegal
};
// EVOLVE-BLOCK-END
