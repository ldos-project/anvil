/* EXPECT: PASS */
/* VERIFY: FAIL */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

float *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(1);
  *p = 1.5f;
  return 0;
}
