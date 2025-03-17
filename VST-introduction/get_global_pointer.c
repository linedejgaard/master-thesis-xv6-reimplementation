struct run {
  struct run *next;
};

struct run *freelist1;


struct run *get_freelist1() {
    return freelist1;
}

// this is kind of working
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
