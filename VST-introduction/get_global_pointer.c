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

// working in progress

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

