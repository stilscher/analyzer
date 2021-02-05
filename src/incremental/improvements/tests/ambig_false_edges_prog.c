#include "racemacros.h"

int x = 0;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

int main(void) {
  int x = 0;
  access(x);
  assert_racefree(x);
  return 0;
}
