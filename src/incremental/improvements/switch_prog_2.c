#include<stdio.h>

  
int main (int p) {
  int x = 0;
  switch (p) {
    case 0: return 111;
    case 1: x = x + 1;
    case 3: break;
    default: return 222;
  }
  return 333;
}

