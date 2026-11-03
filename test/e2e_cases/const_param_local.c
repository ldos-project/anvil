/* EXPECT: PASS */
/* VERIFY: PASS */

/* @Guarantee result == 2 * x */
int twice(const int x) {
  const int y = x * 2;
  return y;
}
