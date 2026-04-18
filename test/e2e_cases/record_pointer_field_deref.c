/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

struct Leaf {
  int value;
};

struct Node {
  struct Leaf *next;
};

struct Leaf leaf0;
struct Node node;
int out;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  leaf0.value = 7;
  node.next = &leaf0;
  out = node.next->value;
  if (!(out == 7)) { abort(); }
  return 0;
}
