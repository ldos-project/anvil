/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>

int xs[1];
int *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = &xs[1];
  *p = 1;
  return 0;
}
