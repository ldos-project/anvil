/* Comparator proof example.
 *
 * Ordinary @Guarantee clauses give a per-call summary of the comparator.
 * @Theorem clauses then state the global order laws concisely in terms of
 * compare_int(...) itself.
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
 * @Theorem forall(int x). compare_int(x, x) = 0
 * @Theorem forall(int x, int y). (compare_int(x, y) = 0) ==> (x = y)
 * @Theorem forall(int x, int y). ((compare_int(x, y) <= 0) || (compare_int(y, x) <= 0))
 * @Theorem forall(int x, int y). (((compare_int(x, y) <= 0) && (compare_int(y, x) <= 0)) ==> (x = y))
 * @Theorem forall(int x, int y, int z). (((compare_int(x, y) <= 0) && (compare_int(y, z) <= 0)) ==> (compare_int(x, z) <= 0))
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

int main(void) {
  return 0;
}
