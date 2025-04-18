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

int while_1_2(int n) { 
    int s = 0;
    while (s + PGSIZE <= n) { 
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

int while_1_3(int n) { 
    int s = 0;
    int c = 0;
    while (s + PGSIZE <= n) { 
        s = s + PGSIZE;
        c++;
    }
    return c;
}

int while_1_4(int n, int s) { 
    int c = 0;
    while (s + PGSIZE <= n) { 
        s = s + PGSIZE;
        c++;
    }
    return c;
}

int for_1_2(int n) {
    int s;
    for (s = 0; s + PGSIZE <= n; s += PGSIZE) {
        // No body needed, since the increment happens in the for loop
    }
    return s;
}

int for_1_3(int n) {
    int s;
    int c = 0;
    for (s = 0; s + PGSIZE <= n; s += PGSIZE) {
        c++;
    }
    return c;
}

int for_1_4(int n, int s) { 
    int c = 0;
    for (; s + PGSIZE <= n; s += PGSIZE) {
        c++;
    }
    return c;
}




int while_1_5(void *pa_start, void *pa_end) {  // admit on pointer
    int c = 0;
    while ((char*)pa_start + PGSIZE <= (char*)pa_end) { 
        pa_start = (char*)pa_start + PGSIZE;
        c++;
    }
    return c;
}

// wokring in progress

int while_1_6(void *pa_start, void *pa_end)
{
    char *p = (char*)pa_start;
    int c = 0;
    while (p + PGSIZE <= (char*)pa_end) { 
        p = p + PGSIZE;
        c++;
    }
    return c;
}




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

