/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

int xs[4];
int *p;
int y;

int main(void) {
  p = &xs[1];
  xs[0] = 3;
  xs[1] = (xs[0] + 4);
  p[1] = (xs[1] + 1);
  y = p[1];
  return 0;
}
