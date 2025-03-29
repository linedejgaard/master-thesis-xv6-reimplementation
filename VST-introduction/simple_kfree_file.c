
struct run {
  struct run *next;
};

struct run *freelist1;


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

void call_kfree1(void *pa) 
{
  kfree1(pa);
}

void call_kfree1_if_1(void *pa) 
{
  if (pa) // check if pa is NULL
    kfree1(pa);
}

void freerange_no_loop_no_add(void *pa_start, void *pa_end) {
  if (pa_start <= pa_end)
    kfree1(pa_start);
}


#define PGSIZE 4096 // bytes per page

void freerange_no_loop_no_add_1(void *pa_start, void *pa_end) {
  if (((char*)pa_start + PGSIZE)<=(char*)pa_end) 
    kfree1(pa_start);
}

int while_1_5(void *pa_start, void *pa_end) {  // admit on pointer
  int c = 0;
  while ((char*)pa_start + PGSIZE <= (char*)pa_end) { 
      pa_start = (char*)pa_start + PGSIZE;
      c++;
  }
  return c;
}

// working in progress...


void freerange_while_loop(void *pa_start, void *pa_end) {  // admit on pointer
  while ((char*)pa_start + PGSIZE <= (char*)pa_end) { 
      pa_start = (char*)pa_start + PGSIZE;
      kfree1(pa_start);
  }
}





// working in progress


int while_sum(void *pa_start, void *pa_end)
{
  char *p = (char*)pa_start;
  int n = 0;
  while (p + PGSIZE <= (char*)pa_end) {
    n++;
    p += PGSIZE;
  }
  return n;
}

void freerange_while_1(void *pa_start, void *pa_end)
{
  char *p = (char*)pa_start;
  while (p + PGSIZE <= (char*)pa_end) {
    kfree1(p);
    p += PGSIZE;
  }
}


void freerange_loop_1(void *pa_start, void *pa_end)
{
  char *p;
  p = (char*)pa_start;
  for(; p + PGSIZE <= (char*)pa_end; p += PGSIZE)
    kfree1(p);
}

