/* EXPECT: PASS */
/* VERIFY: PASS */
#include <stdlib.h>
#include <stdio.h>

int x;

int main(void) {
  while (x < 3) {
    x = (x + 1);
  }
  return 0;
}
