/* Quantified contract example that should fail. */

#include <stdlib.h>
#include <stdio.h>

/* @Contract bump_bad
 * @Guarantee forall(int i). (((i >= 0) && (i <= x)) ==> (result > i))
 */
int bump_bad(int x) {
  return x;
}

int main(void) {
  return 0;
}
