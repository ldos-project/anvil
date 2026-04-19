// EVOLVE-BLOCK-START

config.add_listeners(varG, {
    vulcan::listeners::global::RollingWindow(10)
});

config.add_listeners(varO, {
    vulcan::listeners::object::EWMA({0.1})
});

// requirement: output must always be either 0, 1, or 2
SCORING_FN(const vulcan::feature_store& fs, int64_t obj_id) {
    return fs.get_latest(varG) + fs.get_ewma(varO, obj_id, 0.1); // this is not always going to be 0, 1, or 2 - could be any float.
};
// EVOLVE-BLOCK-END