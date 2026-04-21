/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

double *p;
double x;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(16);
  *p = 1.25;
  *(p + 1) = 3.5;
  x = ((*p * 2.0) + *(p + 1));
  free(p);
  return 0;
}
