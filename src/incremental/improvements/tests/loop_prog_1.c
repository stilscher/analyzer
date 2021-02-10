#include<stdio.h>

int main (void) {
    int n = 5;
    int x = 1;

    while (n > 0) {
        x = x * n;
        n = n - 1;
    }
    return x;
}
