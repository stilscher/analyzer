// PARAM: --sets solver td3 --set ana.activated "['base','threadid','threadflag','mallocWrapper','octy']"
// Example from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/bitvector-loops/overflow_1-2.c

int main(void) {
  unsigned int x = 10;

  while (x >= 10) {
    x += 2;
  }

  assert(1);
}
