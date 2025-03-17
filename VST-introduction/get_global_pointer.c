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