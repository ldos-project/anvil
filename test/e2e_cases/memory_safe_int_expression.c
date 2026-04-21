/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

int *p;
int x;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(8);
  *p = 3;
  *(p + 1) = 4;
  x = ((*p * 2) + *(p + 1));
  free(p);
  return 0;
}
