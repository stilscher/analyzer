
#include <stdio.h>
//source base: https://stackoverflow.com/questions/4007268/what-exactly-is-meant-by-de-referencing-a-null-pointer
int main(){  
    int arr[] = {1, 2, 3, 4, 5, 6};
    int a, b, c, x; // some integers
    int *pi;     // a pointer to an integer
    int *ok;
    a = arr[2];
    ok = &a;
    pi = &a; // pi points to a
    b = *pi; // b is now 5
    pi = NULL;
    c = *ok; //NOWARN
    c = *pi; // WARN
    arr[3] = NULL; //WARN
    x = arr[3];
    c = x; //WARN

    return 1;
}