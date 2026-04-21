/* EXPECT: PASS */
/* VERIFY: PASS */
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
    return 5;
  } else {
    return -5;
  }
}

int main(void) {
  int pos;
  int neg;

  pos = signed_from_bit(true);
  neg = signed_from_bit(false);
  if (!(pos > 0)) {
    abort();
  }
  if (!(neg < 0)) {
    abort();
  }
  return 0;
}
