/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

bool *p;
bool x;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(2);
  *p = true;
  *(p + 1) = false;
  x = (*p + *(p + 1));
  free(p);
  return 0;
}
