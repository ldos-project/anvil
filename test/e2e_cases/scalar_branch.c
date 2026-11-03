/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>

int x;

int main(void) {
  if (x == 0) {
    x = 1;
  } else {
    x = 2;
  }
  return 0;
}
