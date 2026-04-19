// EVOLVE-BLOCK-START

// violation: can't allocate memory
float* values = (float*) malloc(10 * sizeof(float));

config.add_listeners(varG, {
    vulcan::listeners::global::RollingWindow(10)
});

SCORING_FN(const vulcan::feature_store& fs, int64_t obj_id) {
    values[obj_id] = fs.get_latest(varG); // no error because our template uses only two objects
    return *values; // illegal
};
// EVOLVE-BLOCK-END
