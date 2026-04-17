/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

int *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(1);
  *p = 7;
  return 0;
}
