/* EXPECT: PASS */
/* VERIFY: PASS */
#include "modular_stub_contracts.h"
#include <stdlib.h>
#include <stdio.h>

int x;

/* @Require y >= 0
 * @Guarantee result > y
 * @Safety y >= 0
 */
int bump(int y) {
  return (y + 1);
}

int main(void) {
  // @Safety x >= 0
  x = bump(1);
  x = external_step(x);
  return 0;
}
