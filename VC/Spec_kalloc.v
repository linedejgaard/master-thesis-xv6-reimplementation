(** * Spec_stack: VSU specification of the Stack module *)

(** Recall the Stack module described in [Verif_stack].  Recall that
   [stack.c] really contained two modules, "stack" and "triang".  We 
   will break this program into four pieces, as follows:

 - [stdlib.c]  (and [stdlib.h]) characterizing the external library functions, malloc, free, exit. 
 - [stack2.c]  (and [stack2.h]) with newstack, push, pop.
 - [triang2.c] (and [triang2.h]) with push_increasing, pop_and_add, and triang.
 - [main2.c] with a main function that calls triang.

For the [stack] module we have the header file [stack2.h]: 

    /* stack2.h */
    #include <stddef.h>
    struct stack;
    struct stack *newstack(void);
    void push (struct stack *p, int i);
    int pop (struct stack *p);
*)

(* ################################################################# *)
(** * Let's verify! *)

Require Import VST.floyd.proofauto.
Require Import VC.kalloc.
