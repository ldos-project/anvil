/* EXPECT: PASS */
/* VERIFY: PASS */

/* @Guarantee result >= -1 && result <= 1 */
int sign(int x) {
  if (x > 0)
    return 1;
  else if (x < 0)
    return -1;
  else
    return 0;
}
