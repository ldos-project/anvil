#define SCORING_FN(fs_param, obj_param) auto scoring_fn = [&](fs_param, obj_param) -> double
#include "vulcan.h"
#include <iostream>
#include <vector>
#include <string>

int main() {
    vulcan::feature_registry registry;
    
    // setup of global + per object features
    auto varG = registry.global.declare_f64("varA", "variable A");
    auto varO = registry.object.declare_f64("varO", "variable O");
    vulcan::rank_config config;
    
    #include "LLMCode.h"

    config.set_sorting_function(vulcan::rank::FullSort);
    config.set_scoring_fn(scoring_fn);
    config.set_comparator(vulcan::min);

    auto basic_rank_policy = vulcan::instantiate_rank_policy(registry, config);
    vulcan::feature_store& store = basic_rank_policy.get_feature_store();
    for (int i=0; i<5; i++) basic_rank_policy.add_object(i); 
    
    for (int t = 0; t < 5; ++t) {
        store.update(varG, 6.2 * t);
        for(int i=0; i<5; i++) store.update(varO, i, i * t);
        int64_t best_obj = vulcan::decision(basic_rank_policy);
        std::cout << "Got best decision: " << best_obj << std::endl;
    }
    return 0;
}