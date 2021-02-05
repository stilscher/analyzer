#include<stdio.h>

int main (void) {
    int n = 5;
    int x = 1;
    
    if (n > 0) {
        return x;
    }
    x = x * n;
    n = n - 1;
}
