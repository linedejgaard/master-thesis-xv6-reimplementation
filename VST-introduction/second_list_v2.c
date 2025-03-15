struct node {
  struct node *next;
};

struct {
  struct node *freelist;
} kmem;

struct node *add(struct node *head, struct node *tail) {
  if (!head) {
    // Handle malloc failure or invalid list pointer
    return 0;
  }
  if (!tail) {
    return 0;
  }
  head->next = tail;
  return head;
}


struct node *add_void(void *p, struct node *tail) {
  if (!tail) {
    return 0;
  }
  struct node *head;
  head = (struct node*) p;

  head->next = tail;
  return head;
}

struct node *add_kmem(void *p) {
  if (!kmem.freelist) {
    return 0;
  }
  struct node *head;
  head = (struct node*) p;

  head->next = kmem.freelist;
  return head;
}


int main() {
}