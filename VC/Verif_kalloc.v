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
Require Import VC.hints.  (* Import special hints for this tutorial. *)




(*  
    - Functional model (often in the form of a Coq function)
    - API specification
    - Function-body correctness proofs, one per file. 
*)

(* Functional model *)
(* Define the type of memory addresses *)
Definition addr := nat.

(* Define a structure to represent a 'run' as a linked list *)
Inductive run :=
  | Run : addr -> option run -> run.

(* Define a structure to represent the memory allocator state *)
Record kmem := {
  lock : bool;            (* Indicates whether the lock is acquired or not *)
  freelist : option run;  (* Pointer to the free list of memory blocks *)
}.

(*Definition lock : base.val :=
  λ: "l", repeat (CAS "l" unlocked locked).
*)
(*Definition isLock (l : loc) J : vPred :=
  ((Rel l (Q J) Q_dup)
  ∗ (RMWAcq l (Q J) Q_dup)
  ∗ (Init l)
  ).
*)


(* Lock acquisition function *)
Definition acquire (kmem : kmem) :=
  {| lock := true; freelist := kmem.(freelist) |}.

(* Lock release function *)
Definition release (kmem : kmem) :=
  {| lock := false; freelist := kmem.(freelist) |}.

(* Free a page of memory, ensuring locking discipline *)
Definition kfree (kmem : kmem) (p : addr) :=
  (* Create a new run node for the freed page.
    - `p` is the address of the freed page.
    - `kmem.(freelist)` is the current free list (possibly empty).
    - This effectively pushes `p` onto the free list. *)
  let new_run := Run p kmem.(freelist) in
  (* Return a new kmem record with:
      - The same lock state.
      - An updated freelist with `new_run` at the head. *)
  {| lock := kmem.(lock); freelist := Some new_run |}.

(* Safe kfree: Ensures the lock is held before modifying *)
Definition safe_kfree (kmem : kmem) (p : addr) :=
  let kmem_locked := acquire kmem in  (* Acquire lock *)
  let kmem_freed := kfree kmem_locked p in (* Perform free *)
  release kmem_freed.  (* Release lock *)

(* Allocate a page, ensuring locking discipline *)
Definition kalloc (kmem : kmem) :=
  let kmem_locked := acquire kmem in (* Acquire lock *)
  match kmem_locked.(freelist) with
  | None => (None, release kmem_locked) (* No available memory *)
  | Some (Run p next) =>
      (Some p, release {| lock := kmem_locked.(lock); freelist := next |}) (* Allocate *)
  end.





(* Free a page of memory, add it to the freelist *)
(*Definition kfree (kmem : kmem) (p : addr) :=

  let new_run := Run p kmem.(freelist) in
  
  {| lock := kmem.(lock); freelist := Some new_run |}.*)





(* Inductive definition of linked lists (the freelist) *)
Definition t_list := Tstruct _run noattr.



(* Representation of the list and lemmas *)
Fixpoint listrep (sigma: list val) (p: val) : mpred :=
 match sigma with
 | h::hs =>
    EX y:val,  
        data_at Tsh t_list (y) p * listrep hs y
 | nil =>
    !! (p = nullval) && emp
 end.

Arguments listrep sigma p : simpl never.


Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
intros.
revert p; induction sigma; intros p; unfold listrep.
- entailer!. split; auto.
- fold listrep. Intros y. entailer!.
 split; intro.
 + subst p; eapply field_compatible_nullval; eauto.
 + inversion H2.
Qed.

(** Now we add this lemma to the Hint database called [saturate_local] *)
#[export] Hint Resolve listrep_local_facts : saturate_local.


Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 intros.
 unfold listrep.
 destruct sigma; simpl.
- entailer!.
- Intros y.
  auto with valid_pointer.
Qed.

#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

(* Functional Model *)

Definition trun := Tstruct _run noattr.
Definition tkmem := Tstruct _kmem noattr.

Fixpoint freelistrep (il: list val) (p: val) : mpred :=
  match il with
  | h::t =>
      EX next: val,
      data_at Ews (trun) next p * 
      freelistrep t next
  | nil => !! (p = nullval) && emp
  end.
(*
Definition kmemrep (il : list val) (p: val) : mpred :=
  EX bl: list (list byte * Z),
  !! (contents = map fst bl) &&
  malloc_token Ews thashtable p * 
  data_at Ews thashtable (map snd bl) p 
  * iter_sepcon (uncurry listrep) bl.

Definition hashtable_rep (contents: hashtable_contents) (p: val) : mpred :=
  EX bl: list (list (list byte * Z) * val),
    !! (contents = map fst bl) &&
    malloc_token Ews thashtable p * 
    data_at Ews thashtable (map snd bl) p 
    * iter_sepcon (uncurry listrep) bl.


Definition list_cell (key: list byte) (count: Z) (next: val) (p: val): mpred :=
 EX kp: val, cstring Ews key kp 
             * malloc_token Ews (tarray tschar (Zlength key + 1)) kp
             * data_at Ews tcell (kp,(Vint (Int.repr count), next)) p 
             * malloc_token Ews tcell p.




Definition spinlock_inv lock_ptr := 
  EX locked: val, 
    data_at Ews (Tstruct _spinlock noattr) locked lock_ptr.

Definition kmemrep (il: list val) (p: val) :=
  EX lock_ptr: val, EX freelist_ptr: val,
    malloc_token Ews (Tstruct _kmem noattr) p * 
    data_at Ews (Tstruct _kmem noattr) (lock_ptr, freelist_ptr) p *
    spinlock_inv lock_ptr *
    freelistrep il freelist_ptr.
  


Definition stack (il: list val) (p: val) :=
  EX q:val,
    malloc_token Ews (Tstruct _kmem noattr) p * 
    data_at Ews (Tstruct _kmem noattr)  *
    freelistrep il q.

Definition kmemrep (il: list val) (kmem_ptr: val) : mpred :=
  
  EX freelist: val,
    malloc_token Ews (Tstruct _kmem noattr) kmem_ptr *
    data_at Ews (Tstruct _kmem noattr) (struct_tuple [default_val (Tstruct _spinlock noattr); freelist]) kmem_ptr *
    freelistrep il freelist.




  Definition kmemrep (il: list val) (kmem_ptr: val) : mpred :=
    EX freelist: val,
      data_at Ews (Tstruct _kmem noattr) (default_val (Tstruct _spinlock noattr), freelist) kmem_ptr * 
      freelistrep il freelist.

Definition kmemrep (il: list val) (kmem_ptr: val) : mpred :=
  EX freelist: val,
    data_at Ews (Tstruct _run noattr) freelist kmem_ptr * 
    freelistrep il freelist.
  

(* API specification *)

    (* Specification of freelist *)
Check data_at.
(*
Definition freelist (il : list Z) (p : val)

Definition kfree_spec : ident * funspec :=
 DECLARE _kfree
 WITH t: type, p:val, gv: globals
 PRE [ tptr tvoid ]
     PROP ()
     PARAMS (p)
     SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p)
 POST [ Tvoid ]
     PROP () RETURN () SEP (mem_mgr gv).




Definition reverse_spec : ident * funspec :=
 DECLARE _kfree
  WITH sigma : list val, p: val
  PRE  [ tptr t_list ]
     PROP ()  PARAMS (p)  SEP (listrep sigma p)
  POST [ (tptr t_list) ]
    EX q:val,
     PROP ()  RETURN (q)  SEP (listrep(rev sigma) q).


Definition malloc_spec_example  :=
 DECLARE _malloc
 WITH t:type, gv: globals
 PRE [ tuint ]
    PROP (0 <= sizeof t <= Int.max_unsigned;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    PARAMS (Vint (Int.repr (sizeof t)))
    SEP (mem_mgr gv)
 POST [ tptr tvoid ] EX p:_,
    PROP ()
    RETURN (p)
    SEP (mem_mgr gv;
            if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

Definition free_spec_example :=
 DECLARE _free
 WITH t: type, p:val, gv: globals
 PRE [ tptr tvoid ]
     PROP ()
     PARAMS (p)
     SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p)
 POST [ Tvoid ]
     PROP () RETURN () SEP (mem_mgr gv).*)

(* Function-body correctness proofs *)
*)