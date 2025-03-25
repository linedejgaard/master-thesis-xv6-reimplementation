#define PGSIZE 4096 // bytes per page

int pointer_comparison_1 (void *p, void *q) {
    return ((PGSIZE + (char*)p )<=(char*)q);
}

int pointer_comparison_2 (void *p, void *q) {
    if ((PGSIZE + (char*)p )<=(char*)q) 
        return 42;
    return 13;
}