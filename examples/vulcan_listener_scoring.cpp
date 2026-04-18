/* Whole-program verification, with the scoring hook visually highlighted. */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

namespace vulcan {
  class FeatureRegistry {
    int global_count;
    int object_count;

    int declare_global_i64(int slot) {
      global_count += 1;
      return slot;
    }

    int declare_object_i64(int slot) {
      object_count += 1;
      return slot;
    }
  };

  class RankConfig {
    int switch_penalty;
    int add_global_listener(int feature_slot, int window) {
      return (feature_slot + window);
    }
    int add_object_listener(int feature_slot, int window) {
      return (feature_slot + window);
    }
  };

  class FeatureStore {
    int latency[2];
    int temp[2];
    int prev_decisions;
  };

}
/* @Require latency_slot == 0 && temp_slot == 1 && prev_slot == 2 && obj_id >= 1 && obj_id <= 2 && config.switch_penalty >= 0 && store.latency[0] >= 0 && store.latency[1] >= 0 && store.temp[0] >= 0 && store.temp[1] >= 0 && store.prev_decisions >= 0
 * @Guarantee result >= 0
 * @Safety config.switch_penalty >= 0 && heap_ok ()
 */
int scoring_fn(const vulcan::FeatureStore& store,
               const vulcan::RankConfig& config,
               int latency_slot,
               int temp_slot,
               int prev_slot,
               int obj_id) {
  int latency_value;
  int temp_value;
  int score;

  latency_value = store.latency[(obj_id - 1)];
  temp_value = store.temp[(obj_id - 1)];
  score = (latency_value + temp_value);
  if (store.prev_decisions != obj_id) {
    score += config.switch_penalty;
  }
  return score;
}

int choose_backend(const vulcan::FeatureStore& store,
                   const vulcan::RankConfig& config,
                   int latency_slot,
                   int temp_slot,
                   int prev_slot,
                   int left_id,
                   int right_id) {
  int left_score;
  int right_score;

  left_score = scoring_fn(store, config, latency_slot, temp_slot, prev_slot, left_id);
  right_score = scoring_fn(store, config, latency_slot, temp_slot, prev_slot, right_id);
  if (left_score <= right_score) {
    return left_id;
  } else {
    return right_id;
  }
}

int main(void) {
  vulcan::FeatureRegistry registry;
  vulcan::RankConfig config;
  vulcan::FeatureStore store;
  int latency_slot;
  int temp_slot;
  int prev_slot;
  int choice;
  int setup_token;

  latency_slot = 0;
  temp_slot = 1;
  prev_slot = 2;

  config.switch_penalty = 20;
  setup_token = registry.declare_object_i64(latency_slot);
  setup_token = registry.declare_object_i64(temp_slot);
  setup_token = registry.declare_global_i64(prev_slot);
  setup_token = config.add_global_listener(prev_slot, 1);
  setup_token = config.add_object_listener(latency_slot, 5);
  setup_token = config.add_object_listener(temp_slot, 5);

  store.latency[0] = 12;
  store.latency[1] = 18;
  store.temp[0] = 30;
  store.temp[1] = 22;
  store.prev_decisions = 1;

  choice = choose_backend(store, config, latency_slot, temp_slot, prev_slot, 1, 2);
  return 0;
}
