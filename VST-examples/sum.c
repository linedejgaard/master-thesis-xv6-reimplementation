#include <stdio.h>

int sum_2_2(void) {
    int a = 2;
    int b = 2;
    int result = a + b;
    return (int)result;
}

int main(void) {
    int result = sum_2_2();
    return result;
}