struct node {
  struct node *next;
};



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

void free(void *pa, struct node *tail) // LINE: kind of add ( push) -- more similar to kfree, just don't use locks nor global variables..
{
  struct node *r;

  r = (struct node*)pa;

  r->next = tail;
  tail = r;
}



//  remove - not verified..

struct node *remove(struct node *tail) {

  struct node *head;
  head = tail;

  if (head) 
    tail = head->next;

  return (struct node*)tail;
}



/// wait with this..

struct {
  struct node *freelist;
} kmem;

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