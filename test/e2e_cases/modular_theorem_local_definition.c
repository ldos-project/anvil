/* EXPECT: PASS */
/* VERIFY: PASS */
#include "modular_theorem_local_contracts.h"
#include <stdlib.h>
#include <stdio.h>

/* Local definitions should inherit theorem clauses from the imported header
 * and have them checked against the implementation during verification.
 */
/* @Contract id
 * @Guarantee result = x
 */
int id(int x) {
  int y;
  y = x;
  return y;
}

int main(void) {
  return id(0);
}
