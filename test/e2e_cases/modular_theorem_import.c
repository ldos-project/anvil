/* EXPECT: PASS */
/* VERIFY: PASS */
#include "modular_theorem_import_contracts.h"
#include <stdlib.h>
#include <stdio.h>

/* Client-side wrapper that is meant to rely on the imported theorem.
 * The local theorem is stronger than the local guarantee: it follows from
 * the equality-style summary here plus the imported theorem on external_bump.
 */
/* @Contract use_external_bump
 * @Guarantee result = external_bump(x)
 * @Theorem forall(int x). use_external_bump(x) > x
 */
int use_external_bump(int x) {
  return external_bump(x);
}

int main(void) {
  return 0;
}
