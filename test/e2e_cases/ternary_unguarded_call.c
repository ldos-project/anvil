/* EXPECT: PASS */
/* VERIFY: FAIL */

/* @Require d > 0
 * @Guarantee result >= 0 */
int half(int d) {
  return d / 2;
}

/* `y == 0` takes the branch that calls `half(0)`. */
/* @Guarantee result >= 0 */
int half_or_zero(int y) {
  return y >= 0 ? half(y) : 0;
}
