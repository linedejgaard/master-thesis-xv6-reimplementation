
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

