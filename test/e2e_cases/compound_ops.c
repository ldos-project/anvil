/* EXPECT: PASS */
/* VERIFY: PASS */

/* @Require x >= 0
 * @Guarantee result == x */
int round_trip(int x) {
  int y = x;
  y *= 4;
  y /= 2;
  --y;
  y++;
  y /= 2;
  return y;
}
