/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

int out;

int main(void) {
  int xs[2];
  int *p;
  p = &xs[0];
  p[1] = 7;
  out = xs[1];
  return 0;
}
