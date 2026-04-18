/* A small C++-flavored ranking policy in Anvil's current subset. */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

namespace policysmith {
  class Request {
    int bytes;
    bool latency_sensitive;
  };

  class Backend {
    int id;
    int queue_depth;
    int temperature;
    bool healthy;
  };

  int request_boost(const Request& request) {
    if (request.latency_sensitive) {
      return 0;
    } else {
      return 15;
    }
  }

  int backend_cost(const Backend& backend) {
    int cost;
    cost = (backend.queue_depth + backend.temperature);
    if (backend.healthy) {
      return cost;
    } else {
      return (cost + 50);
    }
  }

  /* @Require observed_load >= 0
   * @Guarantee result >= observed_load
   * @Safety observed_load >= 0
   */
  int penalty(int observed_load) {
    return observed_load;
  }

  int penalty(bool switching) {
    if (switching) {
      return 20;
    } else {
      return 0;
    }
  }

  class Router {
    int previous_id;

    int score(const Backend& backend, const Request& request, int observed_load) {
      int base;
      base = ((backend_cost(backend) + request_boost(request))
              + penalty(observed_load));
      if (previous_id != backend.id) {
        return (base + penalty(true));
      } else {
        return (base + penalty(false));
      }
    }

    int record(int& slot, int chosen) {
      slot = chosen;
      previous_id = chosen;
      return slot;
    }

    int choose(const Backend& left,
               const Backend& right,
               const Request& request,
               int observed_load,
               int& slot) {
      int left_score;
      int right_score;
      left_score = score(left, request, observed_load);
      right_score = score(right, request, observed_load);
      if (left_score <= right_score) {
        return record(slot, left.id);
      } else {
        return record(slot, right.id);
      }
    }
  };
}

policysmith::Request request;
policysmith::Backend fast_drive;
policysmith::Backend cool_drive;
policysmith::Router router;
policysmith::Router *router_ptr;
int chosen_backend;

int main(void) {
  int observed_load;

  request.bytes = 4096;
  request.latency_sensitive = true;

  fast_drive.id = 1;
  fast_drive.queue_depth = 4;
  fast_drive.temperature = 22;
  fast_drive.healthy = true;

  cool_drive.id = 2;
  cool_drive.queue_depth = 8;
  cool_drive.temperature = 17;
  cool_drive.healthy = true;

  router.previous_id = 1;
  router_ptr = &router;
  observed_load = 3;
  chosen_backend = router_ptr->choose(fast_drive, cool_drive, request, observed_load, chosen_backend);
  return 0;
}
