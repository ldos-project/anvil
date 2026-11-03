/* EXPECT: PASS */
/* VERIFY: PASS */

/* @Guarantee result >= 0 */
int abs_val(int x) {
  return x < 0 ? -x : x;
}
