/* EXPECT: PASS */
/* VERIFY: PASS */

/* @Require n >= 0
 * @Guarantee result == n * (n - 1) / 2 */
int sum_below(int n) {
  int total = 0;
  /* @Invariant 0 <= i && i <= n && total == i * (i - 1) / 2 */
  for (int i = 0; i < n; i++)
    total += i;
  return total;
}
