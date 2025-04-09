struct b {int y1;};

struct b p;

int get(void) {
  int i;
  i = p.y1;
  return i;
}

void set(int i) {
  p.y1 = i;
}

int main(void)
{
  set(42);
  int result = get();
  return result;
}
