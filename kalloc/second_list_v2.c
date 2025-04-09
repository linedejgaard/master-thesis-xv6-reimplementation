struct node {
  struct node *next;
};


// add

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

// remove

struct node *remove(struct node *lst) {

  struct node *head;
  head = lst;

  //if (head) 
  lst = head->next;

  return (struct node*)lst;
}

void remove_only_if_lst(struct node *lst) {

  struct node *head;
  head = lst;

  if (head) 
    lst = head->next;

  //return (struct node*)lst;
}

void *alloc(struct node *lst) { 
  struct node *head;
  head = lst;

  if (head) 
    lst = head->next;

  return (struct node*)head;
}


/// wait with this..

struct {
  struct node *freelist;
} kmem;

struct node *get_freelist() {
  return kmem.freelist;
}

void kfree(void *pa) // LINE: kind of add ( push)
{
  struct node *r;

  r = (struct node*)pa;

  r->next = kmem.freelist;
  kmem.freelist = r;
}


int main() {
}