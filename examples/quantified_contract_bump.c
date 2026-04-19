/* Quantified contract example that should verify. */

#include <stdlib.h>
#include <stdio.h>

/* @Contract bump
 * @Guarantee forall(int i). (((i >= 0) && (i <= x)) ==> (result > i))
 * @Guarantee forall(int* p). (is_null(p) || !is_null(p))
 */
int bump(int x) {
  return (x + 1);
}

int main(void) {
  return 0;
}
