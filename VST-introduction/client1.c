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
  if (r) { // this line is not working for client11111
    r->next = kmem.freelist;
    kmem.freelist = r;
  }
  
}

void *kalloc1(void) 
{
  struct run *r;
  r = kmem.freelist;
  if(r)
    kmem.freelist = r->next;
  return (void*)r;
}

// not added to client 1 yet -- it is in simple-kfree
void freerange_while_loop(void *pa_start, void *pa_end) {  // admit on pointer
  while ((char*)pa_start + PGSIZE <= (char*)pa_end) { 
      kfree1(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
  }
}

// should return pa
void *client1(void *pa) {
  kfree1(pa);
  return kalloc1();
}



// should return pa1
void *client2(void *pa1, void *pa2) {
  kfree1(pa1);
  kfree1(pa2);
  kalloc1();
  return kalloc1();
}


// should return pa2
void *client3(void *pa1, void *pa2) {
  kfree1(pa1);
  kfree1(pa2);
  return kalloc1();
}

void *client4(void *pa1, void *pa2) {
  client1(pa1);
  return client1(pa2);
}

void *client5(void *pa1, void *pa2) {
  kfree1(pa1);
  kalloc1();
  kfree1(pa2);
  return kalloc1();
}

void *client6(void *pa_start) {
  int i = 0;
  while (i < 2) {
      kfree1(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
  return kalloc1();
}

void *client7(void *pa_start, int n) {
  int i = 0;
  while (i < n) {
      kfree1(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
  return kalloc1();
}

void client8(void *pa_start, int n) {
  int i = 0;
  while (i < n) {
      kfree1(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
}

// this is basicly doing the same as client 7
void* client9(void *pa_start, int n) {
  client8(pa_start, n);
  return kalloc1();
}

// this is allowed..
void client10(void *pa_start) {
  kfree1(pa_start);
  kfree1(pa_start);
}


// working in progress.. simple version of pipealloc without allocating the files..


#define PIPESIZE 512
typedef unsigned int   uint;

struct pipe {
  char data[PIPESIZE];
  uint nread;     // number of bytes read
  uint nwrite;    // number of bytes written
  int readopen;   // read fd is still open
  int writeopen;  // write fd is still open
};

// very simple - just to check if it can be used for a pipe..
void client_11_pipealloc()
{
  struct pipe *pi;

  pi = 0;
  pi = (struct pipe*)kalloc1();
  if(pi) {
    pi->readopen = 1;
    pi->writeopen = 1;
    pi->nwrite = 0;
    pi->nread = 0;
  }
}





