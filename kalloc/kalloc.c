// Physical memory allocator, for user processes,
// kernel stacks, page-table pages,
// and pipe buffers. Allocates whole 4096-byte pages.

//void freerange(void *pa_start, void *pa_end);

//extern char end[]; // first address after kernel.
                   // defined by kernel.ld.

struct run {
  struct run *next;
};

struct struct_kmem { // Rocq wants it to be named
  int xx; 
  struct run *freelist; 
} kmem;

/* void
freerange(void *pa_start, void *pa_end)
{
  char *p;
  p = (char*)PGROUNDUP((uint64)pa_start);
  for(; p + PGSIZE <= (char*)pa_end; p += PGSIZE)
    kfree(p);
}
 */

// Free the page of physical memory pointed at by pa,
// which normally should have been returned by a
// call to kalloc().  (The exception is when
// initializing the allocator; see kinit above.)
void kfree(void *pa) 
{
  struct run *r;
  r = (struct run*)pa;
  if (r) {
    r->next = kmem.freelist;
    kmem.freelist = r;
  }
}

// Allocate one 4096-byte page of physical memory.
// Returns a pointer that the kernel can use.
// Returns 0 if the memory cannot be allocated.
void *kalloc(void)
{
  struct run *r;
  r = kmem.freelist;
  if(r)
    kmem.freelist = r->next;
  return (void*)r; 
}