/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>

int x;
int *p;

int main(void) {
  p = &x;
  *p = 7;
  return 0;
}
