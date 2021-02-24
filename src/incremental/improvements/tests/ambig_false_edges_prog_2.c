#include "racemacros.h"

int x = 0;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

int main(int y) {
  int y = 0;
  int x = 0;
  access(x);
  assert_racefree(x);
  return 1;
}
