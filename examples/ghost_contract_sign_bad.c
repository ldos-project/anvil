/* The same ghost contract, but the false branch violates it. */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

/* @Contract signed_from_bit
 * @Ghost bool bit_is_set = bit != 0
 * @Guarantee bit_is_set ==> result > 0
 * @Guarantee (!bit_is_set) ==> result < 0
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
