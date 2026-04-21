/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>

int x;
int *p;

int main(void) {
  p = &x;
  if (p != 0) {
    *p = 3;
  } else {
    x = 4;
  }
  return 0;
}
