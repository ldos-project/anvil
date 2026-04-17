/* EXPECT: PASS */
#include "modular_memory_stub_contracts.h"
#include <stdlib.h>
#include <stdio.h>

int *p;
int x;

/* @Require heap_ok()
 * @Guarantee can_free(p) && valid_read(p, 4)
 * @Safety heap_ok()
 */
int init_cell(void) {
  p = malloc(1);
  *p = 7;
  return 0;
}

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  x = init_cell();
  x = external_measure();
  free(p);
  if (!(x >= 0)) { abort(); }
  return 0;
}
