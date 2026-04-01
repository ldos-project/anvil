/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>

int x;

/* @Require y >= 0
 * @Guarantee result > y
 * @Safety y >= 0
 */
int inc(int y) {
  return (y + 1);
}

int main(void) {
  x = inc(1);
  return 0;
}
