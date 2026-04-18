/* EXPECT: FAIL */
#include <stdlib.h>
#include <stdio.h>

int peek(const int *p) {
  (void) p;
  return 0;
}

int main(void) {
  return peek(0);
}
