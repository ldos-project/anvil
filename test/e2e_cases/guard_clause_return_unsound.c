/* EXPECT: PASS */
/* VERIFY: FAIL */
/* @Contract f
 * @Guarantee result == 1 */
int f(int x) {
  if (!(x > 0)) { return 0; }
  return 1;
}

int main(void) { return 0; }
