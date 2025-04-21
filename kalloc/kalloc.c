struct run {
  struct run *next;
};

struct struct_kmem { // Rocq wants it to be named
  int xx; // placeholder for the spinlock
  struct run *freelist; 
} kmem;

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


/// clients usage - allocation

int kalloc_write_42(void) {

  int *pa;
  pa = 0;
  pa = (int*)kalloc();           // cast to int pointer
  if (pa) {
    *pa = 42;
    int X = *pa;
    return X;
  }
  return 0;
}

int* kalloc_int_array(int n) {
  int *pa;
  pa = 0;
  pa = (int*)kalloc();           // cast to int pointer
  if (pa) {
    for (int i = 0; i < n; i++) {
      pa[i] = 42;
    }  
    return pa; // Return the array to the allocated array
  }
  return 0;
}

#define PGSIZE 4096 // Page size in bytes (originally defined in risc.h)
#define PIPESIZE 512
typedef unsigned int uint;

struct pipe {
  char data[PIPESIZE];
  uint nread;     // number of bytes read
  uint nwrite;    // number of bytes written
  int readopen;   // read fd is still open
  int writeopen;  // write fd is still open
};


// Simple test function to verify if kalloc can be used to allocate 
// memory for a composed structure like 'struct pipe'

void kalloc_write_pipe()
{
  struct pipe *pi;

  pi = 0;
  pi = (struct pipe*)kalloc(); 
  if(pi) {
    pi->readopen = 1;
    pi->writeopen = 1;
    pi->nwrite = 0;
    pi->nread = 0;
  }
}

/// clients usage - allocation and deallocation

void *kfree_kalloc(void *pa) {
  kfree(pa);
  return kalloc();
}

void kalloc_kfree() {
  void *p;
  p = kalloc();
  kfree(p);
}

int kalloc_write_42_kfree(void) {
  int *pa;
  pa = 0;
  pa = (int*)kalloc();           // cast to int pointer
  if (pa) {
    *pa = 42;
    int X = *pa;
    kfree(pa);
    return X;
  }
  return 0;
}

int kalloc_write_42_kfree_kfree(void) {
  int *pa;
  pa = 0;
  pa = (int*)kalloc();           // cast to int pointer
  if (pa) {
    *pa = 42;
    int X = *pa;
    kfree(pa);
    return X;
  }
  kfree(pa); // make sure it is free and we are back to scratch
  return 0;
}

void *kfree_kalloc_twice(void *pa1, void *pa2) {
  kfree_kalloc(pa1);
  return kfree_kalloc(pa2);
}

void *kfree_kalloc_kfree_kalloc(void *pa1, void *pa2) { 
  kfree(pa1);
  kalloc();
  kfree(pa2);
  return kalloc();
}

// should return pa2 if they are both pointers
void *kfree_kfree_kalloc(void *pa1, void *pa2) { 
  kfree(pa1);
  kfree(pa2);
  return kalloc();
}


void *kfree_kfree_kalloc_kalloc(void *pa1, void *pa2) { 
  kfree(pa1);
  kfree(pa2);
  kalloc();
  return kalloc();
}

void kfree_kfree_same_pointer(void *pa1) { 
  kfree(pa1);
  kfree(pa1);
}



/// clients usage - loops

void *kfree_kfree_kalloc_loop(void *pa_start) { 
  int i = 0;
  while (i < 2) {
      kfree(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
  return kalloc();
}

void kfree_loop(void *pa_start, int n) { 
  int i = 0;
  while (i < n) {
      kfree(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
}

void* kfree_loop_kalloc(void *pa_start, int n) {
  kfree_loop(pa_start, n);
  return kalloc();
}




