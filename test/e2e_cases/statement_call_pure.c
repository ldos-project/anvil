/* EXPECT: PASS */
/* VERIFY: PASS */

int square(int v) {
  return v * v;
}

int main(void) {
  square(3);
  return 0;
}
