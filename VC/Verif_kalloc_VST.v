(** * Verif_kalloc: Memory Allocation ADT implemented by linked lists *)

(** Here is a little C program, [kalloc.c]

    #include "types.h"
    #include "param.h"
    #include "memlayout.h"
    #include "spinlock.h"
    #include "riscv.h"
    #include "defs.h"

    void freerange(void *pa_start, void *pa_end);

    extern char end[]; // first address after kernel.
                      // defined by kernel.ld.

    struct run {
      struct run *next; 
    };

    struct {
      struct spinlock lock;
      struct run *freelist;
    } kmem;

    void
    kinit()
    {
      initlock(&kmem.lock, "kmem");
      freerange(end, (void* )PHYSTOP);
    }

    void
    freerange(void *pa_start, void *pa_end)
    {
      char *p;
      p = (char* )PGROUNDUP((uint64)pa_start);
      for(; p + PGSIZE <= (char* )pa_end; p += PGSIZE)
        kfree(p);
    }

    // Free the page of physical memory pointed at by pa,
    // which normally should have been returned by a
    // call to kalloc().  (The exception is when
    // initializing the allocator; see kinit above.)
    void
    kfree(void *pa) // LINE: kind of add ( push)
    {
      struct run *r;

      if(((uint64)pa % PGSIZE) != 0 || (char* )pa < end || (uint64)pa >= PHYSTOP)
        panic("kfree");

      // Fill with junk to catch dangling refs.
      memset(pa, 1, PGSIZE);

      r = (struct run* )pa;

      acquire(&kmem.lock);
      r->next = kmem.freelist;
      kmem.freelist = r;
      release(&kmem.lock);
    }

    // Allocate one 4096-byte page of physical memory.
    // Returns a pointer that the kernel can use.
    // Returns 0 if the memory cannot be allocated.
    void *
    kalloc(void) // LINE: kind of remove / pop
    {
      struct run *r;

      acquire(&kmem.lock);
      r = kmem.freelist;
      if(r)
        kmem.freelist = r->next;
      release(&kmem.lock);

      if(r)
        memset((char* )r, 5, PGSIZE); // fill with junk
      return (void* )r;
    }

    This program implements a physical memory allocator, for user processes,
    kernel stacks, page-table pages,and pipe buffers. Allocates whole 4096-byte pages.
    - To create a new linked list of free pages
    - To free up pages (add pages to the linked list)
    - To allocate pages (pop pages from the linked list)

    This memory allocator is implemented as a header node ([struct run])
    pointing to a linked list of next cells ([struct next]). *)

(* ================================================================= *)
(** ** Let's verify! *)

Require VC.Preface. (* Check for the right version of VST *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VC.kalloc.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require VC.Verif_kalloc_Fun_Spec.
Require VC.kalloc.
(*  
    - Functional model (often in the form of a Coq function)
    - API specification (also independent from the c-code)
    - Function-body correctness proofs, one per file. 
*)






(* Now you can write the proofs for these specifications using VST *)
Lemma body_kfree: semax_body Vprog Gprog f_kfree kfree_spec.
Proof.
  start_function.
  (* Proof for kfree *)
Admitted.

Lemma body_kalloc: semax_body Vprog Gprog f_kalloc kalloc_spec.
Proof.
  start_function.
  (* Proof for kalloc *)
Admitted.

Lemma body_freerange: semax_body Vprog Gprog f_freerange freerange_spec.
Proof.
  start_function.
  (* Proof for freerange *)
Admitted.

Lemma body_kinit: semax_body Vprog Gprog f_kinit kinit_spec.
Proof.
  start_function.
  (* Proof for kinit *)
Admitted.

(* Add these lemmas to your global program specification *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [kfree_spec; kalloc_spec; freerange_spec; kinit_spec]).