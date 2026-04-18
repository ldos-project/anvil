/* EXPECT: PASS */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

struct Leaf {
  int value;
};

struct Node {
  struct Leaf leaf;
  struct Leaf leaves[2];
  int slots[2];
  struct Leaf *next;
};

struct Leaf leaf0;
struct Node node;
struct Node *np;
struct Leaf *lp;
int out;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  node.leaf.value = 1;
  node.leaves[0].value = 2;
  node.slots[0] = 3;
  np = &node;
  np->leaves[1].value = (node.slots[0] + node.leaf.value);
  out = np->leaf.value;
  out = node.leaves[1].value;
  lp = &node.leaf;
  out = lp->value;
  node.next = &leaf0;
  lp = node.next;
  return 0;
}
