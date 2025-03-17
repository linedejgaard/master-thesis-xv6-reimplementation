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

struct a {int x1; int x2;};
struct b {int y1; struct node *innerlist;};

struct b p;

int get(void) {
  return p.y1;
}







// not verified_


struct {
  int xx; // lock
  struct node *innerlist;
} kmem;

struct node *get_innerlist() {
  return kmem.innerlist;
}

int get_xx_2() {
  return kmem.xx;
}