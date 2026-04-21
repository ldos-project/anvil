/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>

int x;
int y;
int *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  x = 7;
  p = &x;
  *p = (*p + 1);
  y = *p;
  return 0;
}
