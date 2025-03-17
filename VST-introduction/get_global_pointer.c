struct node {
  struct node *next;
};

struct node *freelist1;


struct node *get_freelist1() {
    return freelist1;
}

// this is kind of working
struct node *get_freelist1_input(struct node *fl) {
  return fl;
}

int i;

int get_i() {
  return i;
}

// working in progress

struct struct_kmem { // eaiser that it has a name is isn't anonymous
  int xx; //kind of lock
  struct node *freelist; //kind of freelist
} kmem;

int get_xx(void) {
  return kmem.xx;
}

struct node *get_freelist(void) {
  return kmem.freelist;
}

