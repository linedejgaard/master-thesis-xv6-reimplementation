
int increment(int *num) {
    // Dereference the pointer and increment the value it points to
    (*num)++;
    // Return the incremented value
    return *num;
}

int main() {
    int value = 10;
    int incremented_value = increment(&value);
    return incremented_value;
}