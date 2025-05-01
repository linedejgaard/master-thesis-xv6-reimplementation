#include <stdio.h>

int sum(int a, int b) {
    int result = a + b;
    return (int)result;
}

int main(void) {
    int result = sum(2, 2);
    return result;
}