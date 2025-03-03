(** * VSU_stack: VSU verification of the Stack module *)
 
(* ================================================================= *)
(** ** stack2.c

    The module stack2.c is slightly adjusted from stack.c; it uses an
  internal function surely_malloc, just to illustrate how to handle
  local functions that are not exported in the ASI module interface.

    #include <stddef.h>
    #include "stdlib.h"
    #include "stack2.h"

    struct cons { int value; struct cons *next; };

    struct stack { struct cons *top; };

    void *surely_malloc (size_t n) {
      void *p = malloc(n);
      if (!p) exit(1);
      return p;
    }

    struct stack *newstack(void) {
      struct stack *p;
      p = (struct stack * ) surely_malloc(sizeof (struct stack));
      p->top = NULL;
      return p;
    }

    void push (struct stack *p, int i) {
      struct cons *q;
      q = (struct cons * ) surely_malloc(sizeof (struct cons));
      q->value = i;
      q->next = p->top;
      p->top = q;
    }

    int pop (struct stack *p) {
      struct cons *q;
      int i;
      q = p->top;
      p->top = q->next;
      i = q->value;
      free(q);
      return i;
    }
*)

(* ################################################################# *)
(** * Building the VSU

    Now we can verify the implementations of the individual modules.
  That is, for each module, we produce a VSU, a Verified Software Unit.
  
  Each of these verifications imports only ASIs (abstract specification
  interfaces), not other VSUs; that is, the verification of a module
  depends only on interfaces, not on the implementations (or
  verifications) of other modules.

  We start by importing floyd.proofauto, as usual, but also
  the floyd.VSU support. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

(** Next, we import the ASIs of the imported modules, and of this
  module.  Since [stack2.c] uses the malloc/free library (exported
  from our stdlib module), we import [Spec_stdlib] as well
  as [Spec_stack]. *)

Require Import VC.Spec_kalloc.
