struct node {
  int value; // just to make it look like append..
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

int main() {
}