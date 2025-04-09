// should be moved to another file
typedef unsigned long uint64;
#define PGSIZE 4096 // bytes per page
#define KERNBASE 0x80000000L
#define PHYSTOP (KERNBASE + 128*1024*1024)
#define PGROUNDUP(sz)  (((sz)+PGSIZE-1) & ~(PGSIZE-1))

// should be moved to another file

struct run {
  struct run *next;
};

struct run *freelist1;


struct run *get_freelist1() {
    return freelist1;
}

struct run *get_freelist1_input(struct run *fl) {
  return fl;
}

int i;

int get_i() {
  return i;
}

struct struct_kmem { // eaiser that it has a name is isn't anonymous
  int xx; //kind of lock
  struct run *freelist; //kind of freelist
} kmem;

int get_xx(void) {
  return kmem.xx;
}

struct run *get_freelist(void) {
  return kmem.freelist;
}

void free(void *pa, struct run *tail) // LINE: kind of add ( push) -- more similar to kfree, just don't use locks nor global variables..
{
  struct run *r;
  r = (struct run*)pa;
  r->next = tail;
  tail = r;
}

void *alloc(struct run *lst) { 
  struct run *head;
  head = lst;
  if (head) 
    lst = head->next;
  return (struct run*)head;
}

void kfree1(void *pa) // LINE: kind of add ( push)
{
  struct run *r;
  r = (struct run*)pa;
  r->next = kmem.freelist;
  kmem.freelist = r;
}

void *kalloc1(void) 
{
  struct run *r;
  r = kmem.freelist;
  if(r)
    kmem.freelist = r->next;
  return (void*)r;
}

void call_kfree1(void *pa) // LINE: kind of add ( push)
{
  kfree1(pa);
}

void call_kfree1_if_1(void *pa) // LINE: kind of add ( push)
{
  if (pa) // check if pa is NULL
    kfree1(pa);
}

int pointer_compare_0 (int *p, int *q) {
  return (p==q);
}

int pointer_compare_1 (char *p, char *q) {
  return (p==q);
}

int pointer_compare_2 (int *p, int *q) {
  return (p<=q);
}

int pointer_compare_3 (int *p, int *q) {
  if (p<=q)
    return 42;
  return 13;
}

int pointer_compare_4 (char *p, char *q) {
  if (p<=q)
    return 42;
  return 13;
}

int pointer_compare_5 (void *p, void *q) {
  if (p<=q)
    return 42;
  return 13;
}

int pointer_compare_6 (void *pa, void *end) {
  if((char*)pa < end)
    return 42;
  return 13;
}



// working in progress

void freerange_no_loop_no_add(void *pa_start, void *pa_end) {
  if (pa_start <= pa_end)
    kfree1(pa_start);
}




int pointer_compare_70 (void *pa, void *end) {
  if(pa)
    if (end)
      return 42;
  return 13;
}




int pointer_compare_7 (void *pa, void *end) {
  if((char*)pa < end || (pa == end))
    return 42;
  return 13;
}

int pointer_compare_8 (void *pa, void *end) {
  if(((uint64)pa % PGSIZE) != 0)
    return 42;
  return 13;
}


int pointer_compare_9 (void *pa, void *end) {
  if(((uint64)pa % PGSIZE) != 0 || (char*)pa < end)
    return 42;
  return 13;
}


int pointer_compare_10 (void *pa, void *end) {
  if(((uint64)pa % PGSIZE) != 0 || (char*)pa < end || (uint64)pa >= PHYSTOP)
    return 42;
  return 13;
}












void align_pointer (void *pointer) {
  char *p;
  p = (char*)PGROUNDUP((uint64)p);
}




int pointer_compare(void *pa_start, void *pa_end) { 
  char *s = (char*)pa_start;
  char *t = (char*)pa_end;
  if (s <= t)
    return 1;
  return 0;
}

// not working on yet..


void freerange_no_loop(void *pa_start, void *pa_end) {
  char *p = (char*)pa_start;
  if (p + PGSIZE <= (char*)pa_end)
    kfree1(p); // Free the first page if it's within the range
}


void freerange(void *pa_start, void *pa_end)
{
  char *p;
  p = (char*)PGROUNDUP((uint64)pa_start);
  for(; p + PGSIZE <= (char*)pa_end; p += PGSIZE)
    kfree1(p); // TODO: fix: this is kfree1
}


// not verified, but I think this compares the values
int pointer_compare_values (char *p, char *q) {
  return (*p == *q);
}



