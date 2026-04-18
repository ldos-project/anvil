/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>

int *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = 0;
  free(p);
  return 0;
}
