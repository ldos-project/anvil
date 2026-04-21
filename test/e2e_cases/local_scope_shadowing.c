/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>

int x;

int main(void) {
  int y;
  y = 1;
  {
    int y;
    y = 2;
    x = y;
  }
  x = y;
  return 0;
}
