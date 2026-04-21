/* The same guarded contracts, but with a buggy false branch. */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

/* @Contract signed_from_bit
 * @Guarantee bit ==> result > 0
 */
/* @Contract signed_from_bit
 * @Guarantee (!bit) ==> result < 0
 */
int signed_from_bit(bool bit) {
  if (bit) {
    return 7;
  } else {
    return 3;
  }
}

int main(void) {
  return 0;
}
