#include<stdio.h>

int main (void) {
    int n = 5;
    int x = 1;

    a:
    n = n * n;
    b:
    x = x * x;
    
    if (n - x > 0) {
        goto a;
    } else {
        goto b;
    }
    return x;
}
