#define PGSIZE 4096 // bytes per page

int pointer_comparison_1 (void *p, void *q) {
    return ((PGSIZE + (char*)p )<=(char*)q);
}

int pointer_comparison_2 (void *p, void *q) {
    if ((PGSIZE + (char*)p )<=(char*)q) 
        return 42;
    return 13;
}

int pointer_comparison_3 (void *p, void *q) {
    if (((char*)p + PGSIZE)<=(char*)q) 
        return 42;
    return 13;
}

int while_1(int n) {
    int s = 0;
    while (s < n) {
        s++;
    }
    return s;
}

int for_1(int n) {
    int s;
    for (s = 0; s < n; s++) {
        // No body needed, since the increment happens in the for loop
    }
    return s;
}

int while_1_1(int n) {
    int s = 0;
    while (s <= n) { // plus
        s++;
    }
    return s;
}

int while_1_2(int n) { // working in progress..
    int s = 0;
    while (s + PGSIZE <= n) { // plus
        s = s + PGSIZE;
    }
    return s;
}

int for_1_1(int n) {
    int s;
    for (s = 0; s <= n; s++) {
        // No body needed, since the increment happens in the for loop
    }
    return s;
}

// working in progress




// wokring in progress



void * while_2(void *pa_start, void *pa_end) {
    while ((char*)pa_start + PGSIZE <= (char*)pa_end) {
        pa_start = (char*)pa_start + PGSIZE;
    }
    return pa_start;
}

int while_3(void *pa_start, void *pa_end) {
    int s = 0;
    while ((char*)pa_start + PGSIZE <= (char*)pa_end) {
        s++;
        pa_start = (char*)pa_start + PGSIZE;
    }
    return s;
}



// working in progress
int for_2(void *pa_start, void *pa_end) {
    int s = 0;
    for (; (char*)pa_start + PGSIZE <= (char*)pa_end; pa_start = (char*)pa_start + PGSIZE) {
        s++;
    }
    return s;
}

