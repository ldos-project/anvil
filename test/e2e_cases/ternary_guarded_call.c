/* EXPECT: PASS */
/* VERIFY: PASS */

/* @Require d > 0
 * @Guarantee result >= 0 */
int half(int d) {
  return d / 2;
}

/* `half`'s @Require only has to hold on the branch that calls it. */
/* @Guarantee result >= 0 */
int half_or_zero(int y) {
  return y > 0 ? half(y) : 0;
}
