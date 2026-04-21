/* EXPECT: PASS */
/* VERIFY: PASS */
#include "missing_safety_contracts.h"
#include <stdlib.h>
#include <stdio.h>

int x;

int main(void) {
  x = inc_missing_safety(1);
  return 0;
}
