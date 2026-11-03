/* EXPECT: FAIL */
/* VERIFY: FAIL */

/* `bump` writes `g`, which a call statement cannot model, so Anvil rejects
   `wrapper();` instead of treating it as a no-op. */
int g;

int bump(void) {
  g = g + 1;
  return 0;
}

int wrapper(void) {
  int r = bump();
  return r;
}

int main(void) {
  g = 0;
  wrapper();
  return 0;
}
