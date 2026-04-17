/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

double *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(4);
  *p = 1.25;
  return 0;
}
