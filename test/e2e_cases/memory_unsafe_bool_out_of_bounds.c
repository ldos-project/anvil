/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

bool *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(1);
  *(p + 1) = true;
  return 0;
}
