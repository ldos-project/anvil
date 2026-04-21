/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

float *p;
float x;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(8);
  *p = 1.5f;
  *(p + 1) = 2.25f;
  x = ((*p * 2.0f) + *(p + 1));
  free(p);
  return 0;
}
