struct node {
  struct node *next;
};

struct node *freelist;


struct node *get_freelist1() {
    return freelist;
}

// this is kind of working
struct node *get_freelist_input(struct node *fl) {
  return fl;
}

int i;

int get_i() {
  return i;
}

// working in progress

struct kmem {
  int xx; //kind of lock
  struct node *innerlist; //kind of freelist
} kmem_p;

int get_xx(void) {
  return kmem_p.xx;
}

struct node *get_innerlist(void) {
  return kmem_p.innerlist;
}

