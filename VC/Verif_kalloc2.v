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

(*Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VC.kalloc.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Require Import VC.hints.  (* Import special hints for this tutorial. *)
*)

(*---------------------------------------------------------------------------------------------------*)
(* In this file we explain how to do the "list examples" from the
   Chapter on Separation Logic for Sequential Programs in the
   Iris Lecture Notes *)


(* Contains definitions of the weakest precondition assertion, and its basic rules. *)
From iris.program_logic Require Export weakestpre.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Export notation lang.

(* Files related to the interactive proof mode. The first import includes the
   general tactics of the proof mode. The second provides some more specialized
   tactics particular to the instantiation of Iris to a particular programming
   language. *)
From iris.proofmode Require Export proofmode.
From iris.heap_lang Require Import proofmode.

(* The following line imports some Coq configuration we commonly use in Iris
   projects, mostly with the goal of catching common mistakes. *)
From iris.prelude Require Import options.

(*  ---------------------------------------------------------------------- *)



(*  
    - Functional model (often in the form of a Coq function)
    - API specification
    - Function-body correctness proofs, one per file. 
*)

(* ----Functional model---- *)



Section free_list.
Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).

(** Stack without values **)

Definition free_list : val := λ: "_", ref NONEV.
Definition kfree : val :=
  rec: "kfree" "s" :=
    let: "tail" := ! "s" in
    let: "new" := SOME (ref "tail") in
    if: CAS "s" "tail" "new" then #() else "kfree" "s".

Definition kalloc : val :=
  rec: "kalloc" "s" :=
    match: !"s" with
      NONE => NONEV
    | SOME "l" =>
      let: "next" := !"l" in
      if: CAS "s" (SOME "l") "next"
      then SOME #()
      else "kalloc" "s"
    end.

(* Define the state of the linked list of run pointers *)
(*
  xs is a list of pointers,
  hd is kind of the start pointer, 
  and hd' becomes the next pointer?
*)
Fixpoint free_list (hd : val) (xs : list loc) : iProp :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs => ∃ hd', ⌜hd= SOMEV #x⌝ ∗ x ↦ SOMEV hd' ∗ free_list hd' xs  
  (* x ↦ SOMEV hd' means x is pointing to somev hd'.
    hd contains the pointer x
    xs is a list of locations/points
    *)
  end.

Definition empty_list : val := NONEV.


Definition cons : val := (λ: "x" "xs",
  let: "p" := ("x", "xs") in
  SOME (Alloc("p"))).







(* Initialize the linked list *)
Definition mk_kmem : val :=
  λ: <>, ref NONEV.



  Definition reverse : val :=
    λ: "l", reverse_append "l" NONE.
  
Definition kinit : val :=
  λ: <>,
    kmem <- NONEV.



  Definition PGSIZE : Z := 4096.
Definition END : Z := 0x80008000. (* Replace with the actual value from your linker script or map file *)
Definition PHYSTOP : Z := 0x81000000. (* Example value, replace with your actual PHYSTOP address *)




(* Define the namespace for the invariant *)
Definition N := nroot .@ "kmem".

(* Define the invariant for the kmem structure *)
Definition kmem_inv (γ : gname) : iProp Σ :=
  inv N (∃ freelist xs, own γ (Excl (Some freelist)) ∗ isFreeList freelist xs).

Definition kmem_inv (γ : gname) : iProp Σ :=
  inv N (∃ freelist, own γ (Excl (Some freelist)) ∗ isFreeList _freelist).



End free_list.







From iris.heap_lang Require Import lang proofmode notation.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang.lib Require Import lock.

(* Define the state of the memory allocator *)
Record kmem_state := {
  freelist : list loc;
}.

(* Define the initial state *)
Definition kmem_init : kmem_state := {|
  freelist := nil;
|}.

(* Constants for the memory layout *)
Definition PGSIZE : Z := 4096.
Definition end_addr : Z := 0x80008000. (* Replace with the actual value from your linker script or map file *)
Definition phystop : Z := 0x81000000. (* Example value, replace with your actual PHYSTOP address *)

(* Generate a list of free memory addresses between end_addr and phystop *)
Program Fixpoint generate_freelist (end_addr phystop : Z) {measure (Z.to_nat (phystop - end_addr))} : list Z :=
  if Z.ltb end_addr phystop then
    end_addr :: generate_freelist (end_addr + PGSIZE) phystop
  else
    nil.
Next Obligation.
  iIntros (end_addr0 phystop0).
  intros.
  rewrite <- Z2Nat.inj_lt; try lia.
  replace (phystop0 - (end_addr0 + PGSIZE)) with (phystop0  (end_addr0 + PGSIZE))
  rewrite Nat.sub_add_distr.
  unfold PGSIZE. 
  replace (phystop0 - (end_addr0 + 4096)) with 
  rewrite <- Z2Nat.inj_sub; try lia.
  

  apply Z2Nat.inj_lt; lia.
Defined.
Fixpoint generate_freelist (end_addr phystop : Z) {measure (Z.to_nat (phystop - end_addr))} : list Z :=
  if Z.ltb end_addr phystop then
    end_addr :: generate_freelist (end_addr + PGSIZE) phystop
  else
    nil.
Proof.
  - intros.
    apply Z2Nat.inj_lt; auto with zarith.
    pose proof (Z.mod_pos_bound end_addr PGSIZE ltac:(lia)).
    lia.
  - lia.
Defined.

Fixpoint generate_freelist (end_addr phystop : Z)  :=
  

  if Z.ltb end_addr phystop then
    end_addr :: generate_freelist (end_addr + PGSIZE) phystop
  else
    nil.
Proof.
  - intros.
    apply Z2Nat.inj_lt; auto with zarith.
    pose proof (Z.mod_pos_bound end_addr PGSIZE ltac:(lia)).
    lia.
  - lia.
Defined.
(* Generate a list of free memory addresses between end_addr and phystop *)
Fixpoint generate_freelist (end_addr phystop : loc) : list loc :=
  if (end_addr <? phystop)%Z then
    end_addr :: generate_freelist (end_addr + PGSIZE)%Z phystop
  else
    nil.

(* Define mk_run function used in kfree *)
Definition mk_run (pa : loc) : loc := pa.

(* Define the operations *)

(* Initialize the allocator *)
Definition kinit (end_addr : loc) (phystop : loc) : kmem_state -> kmem_state :=
  fun s =>
    let freelist := generate_freelist end_addr phystop in
    {| freelist := freelist |}.

(* Free a page of memory *)
Definition kfree (pa : loc) (s : kmem_state) : kmem_state :=
  match (pa mod PGSIZE =? 0)%Z, (pa <? end_addr)%Z, (pa >=? phystop)%Z with
  | true, false, false =>
      let r := mk_run pa in
      let freelist := r :: s.(freelist) in
      {| freelist := freelist |}
  | _, _, _ => s (* panic case, state remains unchanged *)
  end.

(* Allocate a page of memory *)
Definition kalloc (s : kmem_state) : option (loc * kmem_state) :=
  match s.(freelist) with
  | nil => None
  | r :: freelist' =>
      let s' := {| freelist := freelist' |} in
      Some (r, s')
  end.

(* Define the properties and invariants *)

(* Invariant: The free list should only contain valid page addresses *)
Definition freelist_invariant (s : kmem_state) : Prop :=
  Forall (fun pa => (pa mod PGSIZE = 0)%Z /\ (pa >= end_addr)%Z /\ (pa < phystop)%Z) s.(freelist).

(* Define the proof goals *)

Lemma kfree_preserves_invariant s pa :
  freelist_invariant s ->
  freelist_invariant (kfree pa s).
Proof.
  (* Proof steps go here *)
Admitted.

Lemma kalloc_preserves_invariant s r s' :
  kalloc s = Some (r, s') ->
  freelist_invariant s ->
  freelist_invariant s'.
Proof.
  (* Proof steps go here *)
Admitted.

(* Additional lemmas and proofs for kinit and freerange *)


(* Generate a list of free memory addresses between end_addr and phystop *)
Fixpoint generate_freelist (end_addr phystop : loc) : list loc :=
  if (end_addr <? phystop)%Z then
    end_addr :: generate_freelist (end_addr + PGSIZE)%Z phystop
  else
    nil.

(* Define mk_run function used in kfree *)
Definition mk_run (pa : loc) : loc := pa.












(* Define the state of the memory allocator *)
Record kmem_state := {
  freelist : list loc;
}.

(* Define the initial state *)
Definition kmem_init : kmem_state := {|
  freelist := nil;
|}.

(* Define the operations *)

(* Initialize the allocator *)
Definition kinit (end_addr : loc) (phystop : loc) : kmem_state -> kmem_state :=
  fun s => (* Implementation depends on the memory layout and the range of addresses *)
    let freelist := generate_freelist end_addr phystop in
    {| freelist := freelist |}.

(* Free a page of memory *)
Definition kfree (pa : loc) (s : kmem_state) : kmem_state :=
  match (pa mod PGSIZE =? 0)%Z, (pa <? end_addr)%Z, (pa >=? phystop)%Z with
  | true, false, false =>
      let r := mk_run pa in
      let freelist := r :: s.(freelist) in
      {| freelist := freelist |}
  | _, _, _ => s (* panic case, state remains unchanged *)
  end.

(* Allocate a page of memory *)
Definition kalloc (s : kmem_state) : option (loc * kmem_state) :=
  match s.(freelist) with
  | nil => None
  | r :: freelist' =>
      let s' := {| freelist := freelist' |} in
      Some (r, s')
  end.

(* Define the properties and invariants *)

(* Invariant: The free list should only contain valid page addresses *)
Definition freelist_invariant (s : kmem_state) : Prop :=
  Forall (fun pa => (pa mod PGSIZE = 0)%Z /\ (pa >= end_addr)%Z /\ (pa < phystop)%Z) s.(freelist).

(* Define the proof goals *)

Lemma kfree_preserves_invariant s pa :
  freelist_invariant s ->
  freelist_invariant (kfree pa s).
Proof.
  (* Proof steps go here *)
Admitted.

Lemma kalloc_preserves_invariant s r s' :
  kalloc s = Some (r, s') ->
  freelist_invariant s ->
  freelist_invariant s'.
Proof.
  (* Proof steps go here *)
Admitted.

(* Additional lemmas and proofs for kinit and freerange *)



Definition PGSIZE : Z := 4096.

(* kmemG definition *)
Class kmemG Σ := {
  kmemG_inv : inG Σ (authR (gmapUR loc (exclR unitO))); (* Auth for freelist *)
  kmemG_map : inG Σ (authR (gmapUR loc unitO));       (* Auth for memory map *)
}.

(* kmem definition as an invariant *)
Definition kmem `{kmemG Σ} : iProp Σ :=
  ∃ freelist, kmem_map ↦ freelist.

Definition kmem `{kmemG Σ} : iProp Σ :=
  "∃ freelist, kmem_map ↦ freelist"%I.

(* kfree operation *)
Definition kfree `{kmemG Σ} (pa : loc) : iProp Σ :=
  "∃ next, kmem_map pa ↦ next"%I.

(* kalloc operation *)
Definition kalloc `{kmemG Σ} : iProp Σ :=
  "∃ pa, kmem_map ↦ pa"%I.

(* Proof of safety properties *)
Lemma kalloc_safe `{kmemG Σ} : 
  kmem ⊢ |==> kalloc.
Proof.
  iIntros "Hkmem".
  (* Allocate a new page and update kmem *)
  iMod (map_alloc _ _ with "Hkmem") as "[Hkmem Halloc]".
  iModIntro. iFrame.
Qed.

Lemma kfree_safe `{kmemG Σ} (pa : loc) :
  kalloc ⊢ |==> kfree pa.
Proof.
  iIntros "Halloc".
  (* Free the page and update freelist *)
  iMod (map_free _ with "Halloc") as "Hkmem".
  iModIntro. iFrame.
Qed.






Definition kmem `{kmemG Σ} : iProp Σ :=
  "∃ freelist, kmem_map ↦ freelist".

(* kfree operation *)
Definition kfree `{kmemG Σ} (pa : loc) : iProp Σ :=
  "∃ next, kmem_map pa ↦ next".

(* kalloc operation *)
Definition kalloc `{kmemG Σ} : iProp Σ :=
  "∃ pa, kmem_map ↦ pa".

(* Proof of safety properties *)
Lemma kalloc_safe `{kmemG Σ} : 
  kmem ⊢ |==> kalloc.
Proof.
  iIntros "Hkmem".
  (* Allocate a new page and update kmem *)
  iMod (map_alloc _ _ with "Hkmem") as "[Hkmem Halloc]".
  iModIntro. iFrame.
Qed.

Lemma kfree_safe `{kmemG Σ} (pa : loc) :
  kalloc ⊢ |==> kfree pa.
Proof.
  iIntros "Halloc".
  (* Free the page and update freelist *)
  iMod (map_free _ with "Halloc") as "Hkmem".
  iModIntro. iFrame.
Qed.






(*************)

Definition PGSIZE : Z := 4096.

(* Memory block representation *)
Record run := {
  next : loc; (* Pointer to next free block *)
}.

(* Global kmem structure *)
Definition kmem : gname := "kmem".

(* Predicate for a valid memory block *)
Definition is_block (l : loc) : iProp Σ :=
  (l ↦{1/2} (InjLV #l)). (* This ensures the block is allocated *)

(* Predicate for the freelist *)
Fixpoint freelist (l : loc) : iProp Σ :=
  match l with
  | null => True
  | _ => ∃ next, l ↦{1/2} (InjLV #next) ∗ freelist next
  end.

(* Memory allocator invariant *)
Definition kmem_inv : iProp Σ :=
  ∃ l, kmem ↦ l ∗ freelist l.

(* Specification for kalloc *)
Lemma wp_kalloc :
  {{ kmem_inv }}
    kalloc #()
  {{ v, kmem_inv ∗ (⌜v = null⌝ ∨ is_block v) }}.
Proof.
  (* Proof goes here *)
Admitted.

(* Specification for kfree *)
Lemma wp_kfree (p : loc) :
  {{ kmem_inv ∗ is_block p }}
    kfree #p
  {{ _, kmem_inv }}.
Proof.
  (* Proof goes here *)
Admitted.


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