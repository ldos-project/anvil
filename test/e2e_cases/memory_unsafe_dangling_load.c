/* EXPECT: PASS */
/* VERIFY: FAIL */
#include <stdlib.h>
#include <stdio.h>

int *p;
int x;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(4);
  *p = 7;
  free(p);
  x = *p;
  return 0;
}
