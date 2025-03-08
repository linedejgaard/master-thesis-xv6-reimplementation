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

From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.

(*  
    - Functional model (often in the form of a Coq function)
    - API specification
    - Function-body correctness proofs, one per file. 
*)

(* ----Functional model---- *)

(* -- inspired by https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/concurrent_stacks/concurrent_stack1.v?ref_type=heads
      CAS - can that represent the lock?
*)

(* Define a constant for PGSIZE, end, and PHYSTOP *)
Definition PGSIZE :  expr := #4096.
Definition END : expr := #0x80008000. (* Replace with the actual value from your linker script or map file *)
Definition PHYSTOP : expr := #0x81000000. (* Example value, replace with your actual PHYSTOP address *)

(* Define the PGROUNDUP function *)
Definition PGROUNDUP : val :=
  λ: "a", ("a" + PGSIZE - #1) `rem` PGSIZE.

Definition kmem : val := λ: "_", ref NONEV.

(* Define the memset function *)
Definition memset : val :=
  rec: "memset" "ptr" "val" "size" :=
    if: "size" = #0 then #()
    else "ptr" <- "val";; "memset" ("ptr" + #1) "val" ("size" - #1).

Definition panic : val :=
      λ: "msg", #().

(* Define the kfree function *)
Definition kfree_rep : val :=
  rec: "kfree_rep" "fl" "pa" :=
    (* Convert pa to an integer for arithmetic operations *)
    let: "pa_int" := "pa" in
    (* Check if the address is valid *)
    if: ((("pa_int" `rem` PGSIZE) ≠ #0) || ("pa_int" < END) || ((PHYSTOP < "pa_int" || PHYSTOP = "pa_int"))) then
      panic "kfree_rep"
    else
      (* Perform memset *)
      memset "pa" #1 PGSIZE;;
      (* Proceed with freeing the memory *)
      let: "tail" := ! "fl" in           (* tail = next; the free list is going to be the tail *)
      let: "new" := SOME (ref "tail") in (* new = r; a pointer to the tail *)
      if: CAS "fl" "tail" "new" then #() else "kfree_rep" "fl" "pa". (* this counts as the lock *)

(* Define the kalloc function *)
Definition kalloc_rep : val :=
  rec: "kalloc_rep" "fl" :=
    match: !"fl" with
      NONE => NONEV
    | SOME "l" =>
      let: "next" := !"l" in
      if: CAS "fl" (SOME "l") "next"
      then
        memset "l" #5 PGSIZE;;
        SOME "l"
      else
        "kalloc_rep" "fl"
    end.

(* Define the freerange function *)
Definition freerange : val :=
  λ: "pa_start" "pa_end" "fl",
    let: "p" := PGROUNDUP "pa_start" in
    (rec: "loop" "p" := (* define loop and call loop with p *)
      if: ("p" + PGSIZE) ≤ "pa_end" then
        kfree_rep "fl" "p";;
        "loop" ("p" + PGSIZE)
      else #()) "p".



