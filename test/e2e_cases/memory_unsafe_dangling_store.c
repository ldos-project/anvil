/* EXPECT: PASS */
/* VERIFY: FAIL */
#include <stdlib.h>
#include <stdio.h>

int *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(4);
  free(p);
  *p = 1;
  return 0;
}
