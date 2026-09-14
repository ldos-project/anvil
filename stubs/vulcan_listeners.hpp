#ifndef ANVIL_VULCAN_LISTENERS_HPP
#define ANVIL_VULCAN_LISTENERS_HPP

/*
 * Importable contracts for Anvil's lowered Vulcan listener surface.
 *
 * This header intentionally uses the mangled helper names that Anvil's
 * frontend resolves to internally. That keeps the file compatible with
 * Anvil's current header-contract loader, which only understands simple
 * prototype syntax plus comment contracts.
 */

/* @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__global__ns__Average(void);

/* @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__global__ns__MinMax(void);

/* @Require window > 0
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__global__ns__RollingWindow(int window);

/* @Require percentile >= 0 && percentile <= 100
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__global__ns__RollingPercentile(int percentile);

/* @Require alpha >= 0 && alpha <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__global__ns__EWMA(double alpha);

/* @Require alpha_fast >= 0 && alpha_fast <= 1 && alpha_slow >= 0 && alpha_slow <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__global__ns__EWMA(double alpha_fast, double alpha_slow);

/* @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__object__ns__Average(void);

/* @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__object__ns__MinMax(void);

/* @Require window > 0
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__object__ns__RollingWindow(int window);

/* @Require percentile >= 0 && percentile <= 100
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__object__ns__RollingPercentile(int percentile);

/* @Require alpha >= 0 && alpha <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__object__ns__EWMA(double alpha);

/* @Require alpha_fast >= 0 && alpha_fast <= 1 && alpha_slow >= 0 && alpha_slow <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__object__ns__EWMA(double alpha_fast, double alpha_slow);

/* @Guarantee result >= 0
 * @Safety 1
 */
int vulcan__ns__listeners__ns__object__ns__PopulationPercentile(void);

/* @Require feature >= 0 && listener_1 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0 && listener_4 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3, int listener_4);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0 && listener_4 >= 0 && listener_5 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3, int listener_4, int listener_5);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0 && listener_4 >= 0 && listener_5 >= 0 && listener_6 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3, int listener_4, int listener_5, int listener_6);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0 && listener_4 >= 0 && listener_5 >= 0 && listener_6 >= 0 && listener_7 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3, int listener_4, int listener_5, int listener_6, int listener_7);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0 && listener_4 >= 0 && listener_5 >= 0 && listener_6 >= 0 && listener_7 >= 0 && listener_8 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3, int listener_4, int listener_5, int listener_6, int listener_7, int listener_8);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0 && listener_4 >= 0 && listener_5 >= 0 && listener_6 >= 0 && listener_7 >= 0 && listener_8 >= 0 && listener_9 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3, int listener_4, int listener_5, int listener_6, int listener_7, int listener_8, int listener_9);

/* @Require feature >= 0 && listener_1 >= 0 && listener_2 >= 0 && listener_3 >= 0 && listener_4 >= 0 && listener_5 >= 0 && listener_6 >= 0 && listener_7 >= 0 && listener_8 >= 0 && listener_9 >= 0 && listener_10 >= 0
 * @Safety 1
 */
void vulcan__ns__rank_config__add_listeners(vulcan__ns__rank_config* this, int feature, int listener_1, int listener_2, int listener_3, int listener_4, int listener_5, int listener_6, int listener_7, int listener_8, int listener_9, int listener_10);

/* @Require feature >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_latest(vulcan__ns__feature_store* this, int feature);

/* @Require feature >= 0 && obj_id >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_latest(vulcan__ns__feature_store* this, int feature, int obj_id);

/* @Require feature >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_avg(vulcan__ns__feature_store* this, int feature);

/* @Require feature >= 0 && obj_id >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_avg(vulcan__ns__feature_store* this, int feature, int obj_id);

/* @Require feature >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_max(vulcan__ns__feature_store* this, int feature);

/* @Require feature >= 0 && obj_id >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_max(vulcan__ns__feature_store* this, int feature, int obj_id);

/* @Require feature >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_min(vulcan__ns__feature_store* this, int feature);

/* @Require feature >= 0 && obj_id >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_min(vulcan__ns__feature_store* this, int feature, int obj_id);

/* @Require feature >= 0 && k >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_kth_recent(vulcan__ns__feature_store* this, int feature, int k);

/* @Require feature >= 0 && obj_id >= 0 && k >= 0
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_kth_recent(vulcan__ns__feature_store* this, int feature, int obj_id, int k);

/* @Require feature >= 0 && pct >= 0 && pct <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_percentile(vulcan__ns__feature_store* this, int feature, double pct);

/* @Require feature >= 0 && obj_id >= 0 && pct >= 0 && pct <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_percentile(vulcan__ns__feature_store* this, int feature, int obj_id, double pct);

/* @Require feature >= 0 && alpha >= 0 && alpha <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_ewma(vulcan__ns__feature_store* this, int feature, double alpha);

/* @Require feature >= 0 && obj_id >= 0 && alpha >= 0 && alpha <= 1
 * @Guarantee result >= 0
 * @Safety 1
 */
double vulcan__ns__feature_store__get_ewma(vulcan__ns__feature_store* this, int feature, int obj_id, double alpha);

#endif
