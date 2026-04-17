/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

char *p;
char x;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(2);
  *p = 'A';
  *(p + 1) = 'b';
  x = ((*p + 2) - *(p + 1));
  free(p);
  return 0;
}
