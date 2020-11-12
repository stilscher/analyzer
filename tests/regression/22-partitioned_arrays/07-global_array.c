// PARAM: --sets solver td3 --enable ana.int.interval --disable exp.fast_global_inits --enable exp.partition-arrays.enabled  --set ana.activated "['base','threadid','threadflag','expRelation']"
int global_array[50];

int main(void) {
  some_func();

  int x = global_array[5];
  assert(x == 0); //UNKNOWN
  assert(x == 42); //UNKNOWN
}


void some_func(void) {
  global_array[0] = 5;

  for(int i=1; i < 50; i++) {
    global_array[i] = 42;
  }

  int x = global_array[0];
  assert(x == 42); //FAIL
}
