/* Comparator proof example.
 *
 * The quantified contract proves that integer <= is a total order.
 * The comparator contract identifies compare_int(x, y) <= 0 with x <= y.
 * The proof harness then lifts those quantified order laws to the comparator.
 */

#include <stdlib.h>
#include <stdio.h>

/* @Contract compare_int
 * @Guarantee (x <= y) ==> (result <= 0)
 * @Guarantee (result <= 0) ==> (x <= y)
 * @Guarantee (y <= x) ==> (result >= 0)
 * @Guarantee (result >= 0) ==> (y <= x)
 * @Guarantee (x == y) ==> (result == 0)
 * @Guarantee (result == 0) ==> (x == y)
 */
int compare_int(int x, int y) {
  if (x < y) {
    return -1;
  }
  if (y < x) {
    return 1;
  }
  return 0;
}

/* @Contract prove_int_le_total_order
 * @Guarantee forall(int a, int b). ((a <= b) || (b <= a))
 * @Guarantee forall(int a, int b). (((a <= b) && (b <= a)) ==> (a == b))
 * @Guarantee forall(int a, int b, int c). (((a <= b) && (b <= c)) ==> (a <= c))
 */
int prove_int_le_total_order(void) {
  return 0;
}

int prove_compare_total_order(int a, int b, int c) {
  int order_theorem;
  int aa;
  int ab;
  int ba;
  int bc;
  int ac;

  order_theorem = prove_int_le_total_order();

  aa = compare_int(a, a);
  ab = compare_int(a, b);
  ba = compare_int(b, a);
  bc = compare_int(b, c);
  ac = compare_int(a, c);

  if (!(aa == 0)) {
    abort();
  }
  if (!((order_theorem == 0) || (order_theorem != 0))) {
    abort();
  }
  if (!((ab <= 0) || (ba <= 0))) {
    abort();
  }
  if (!(!((ab <= 0) && (ba <= 0)) || (a == b))) {
    abort();
  }
  if (!(!((ab <= 0) && (bc <= 0)) || (ac <= 0))) {
    abort();
  }
  return 0;
}

int main(void) {
  return 0;
}
