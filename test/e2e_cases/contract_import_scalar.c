/* EXPECT: PASS */
/* VERIFY: PASS */
#include "scalar_contracts.h"
#include <stdlib.h>
#include <stdio.h>

int x;

int main(void) {
  x = inc(1);
  return 0;
}
