#define PGSIZE 4096 // bytes per page

struct run {
  struct run *next;
};

struct struct_kmem { 
  int xx; 
  struct run *freelist; 
} kmem;

void kfree1(void *pa) 
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

void freerange_while_loop(void *pa_start, void *pa_end) {  // admit on pointer
  while ((char*)pa_start + PGSIZE <= (char*)pa_end) { 
      kfree1(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
  }
}

// should return pa..
void *client1(void *pa) {
  kfree1(pa);
  return kalloc1();
}



