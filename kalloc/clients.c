#define PGSIZE 4096 // bytes per page

struct run {
  struct run *next;
};

struct struct_kmem { 
  int xx; 
  struct run *freelist; 
} kmem;

void kfree(void *pa) 
{
  struct run *r;
  r = (struct run*)pa;
  if (r) { // this line is not working for client11111
    r->next = kmem.freelist;
    kmem.freelist = r;
  }
  
}

void *kalloc(void) 
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
      kfree(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
  }
}

// should return pa
void *client1(void *pa) {
  kfree(pa);
  return kalloc();
}



// should return pa1
void *client2(void *pa1, void *pa2) {
  kfree(pa1);
  kfree(pa2);
  kalloc();
  return kalloc();
}


// should return pa2
void *client3(void *pa1, void *pa2) {
  kfree(pa1);
  kfree(pa2);
  return kalloc();
}

void *client4(void *pa1, void *pa2) {
  client1(pa1);
  return client1(pa2);
}

void *client5(void *pa1, void *pa2) {
  kfree(pa1);
  kalloc();
  kfree(pa2);
  return kalloc();
}


void *client6(void *pa_start) {
  int i = 0;
  while (i < 2) {
      kfree(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
  return kalloc();
}

void *client7(void *pa_start, int n) {
  int i = 0;
  while (i < n) {
      kfree(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
  return kalloc();
}

void client8(void *pa_start, int n) {
  int i = 0;
  while (i < n) {
      kfree(pa_start);
      pa_start = (char*)pa_start + PGSIZE;
      i++;
  }
}

// this is basicly doing the same as client 7
void* client9(void *pa_start, int n) {
  client8(pa_start, n);
  return kalloc();
}

// this is allowed..
void client10(void *pa_start) {
  kfree(pa_start);
  kfree(pa_start);
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
  pi = (struct pipe*)kalloc(); 
  if(pi) {
    pi->readopen = 1;
    pi->writeopen = 1;
    pi->nwrite = 0;
    pi->nread = 0;
  }
}

int client12_42(void) {

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


int client12_42_include_free(void) {

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





