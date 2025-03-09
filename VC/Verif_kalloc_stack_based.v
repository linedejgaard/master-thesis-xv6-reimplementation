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
From VC Require Import specs.
(*  
    - Functional model (often in the form of a Coq function)
    - API specification (also independent from the c-code)
    - Function-body correctness proofs, one per file. 
*)

(* ----> Functional model <---- *)

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

Definition new_kmem : val := λ: "_", ref NONEV.

(* Define the memset function *)
Definition memset : val :=
  rec: "memset" "ptr" "val" "size" :=
    if: "size" = #0 then #()
    else "ptr" <- "val";; "memset" ("ptr" + #1) "val" ("size" - #1).

Definition panic : val :=
      λ: "msg", #().

(* Define the kfree function *)
Definition kfree_rep : val :=
  rec: "kfree_rep" "fl":=
    (* Convert pa to an integer for arithmetic operations *)
    let: "pa_int" := "fl" in
    (* Check if the address is valid *)
    if: ((("pa_int" `rem` PGSIZE) ≠ #0) || ("pa_int" < END) || ((PHYSTOP < "pa_int" || PHYSTOP = "pa_int"))) then
      panic "kfree_rep"
    else
      (* Perform memset *)
      memset "pa" #1 PGSIZE;;
      (* Proceed with freeing the memory *)
      let: "tail" := ! "fl" in           (* tail = next; the free list is going to be the tail *)
      let: "new" := SOME (ref "tail") in (* new = r; a pointer to the tail *)
      if: CAS "fl" "tail" "new" then #() else "kfree_rep" "fl". (* this counts as the lock *)

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
Definition freerange_rep : val :=
  λ: "pa_start" "pa_end" "fl",
    let: "p" := PGROUNDUP "pa_start" in
    (rec: "loop" "p" := (* define loop and call loop with p *)
      if: ("p" + PGSIZE) ≤ "pa_end" then
        kfree_rep "fl" "p";;
        "loop" ("p" + PGSIZE)
      else #()) "p".


(* --> API Specifications <-- *)

Section freelist.
  Context `{!heapGS Σ} (N : namespace).
  Implicit Types l : loc.


(* option loc to value *)
Definition option_loc_to_val (ol: option loc) : val :=
  match ol with
  | None => NONEV
  | Some loc => SOMEV (#loc)
  end.
(* Inj Type Class: The Inj type class is used to express injectivity of a function. Specifically, Inj R1 R2 f means that if f x1 and f x2 are related by R2, then x1 and x2 must be related by R1. *)
(* Global Instance is available throughout the entire Coq development. Local Instance, on the other hand, is only available within the scope where it is declared. *)
Local Instance option_loc_to_val_inj : Inj (=) (=) option_loc_to_val.
Proof. intros [|][|]; simpl; congruence. Qed.


(*
  The `is_list_pre` function is used to define a recursive predicate for a linked list.
    P: A predicate (val → iProp Σ) on values (val), which specifies the properties that each element in the list should satisfy.
    F: A non-expansive function (option loc -d> iPropO Σ) that defines the predicate for the rest of the list (the tail).
    
    - Returns a non-expansive function of type `option loc -d> iPropO Σ` that describes the properties of the entire list.
    The function returns another non-expansive function (option loc -d> iPropO Σ) that takes an option loc and returns an Iris proposition (iPropO Σ).
*)
Definition is_list_pre (F : option loc -d> iPropO Σ) : option loc -d> iPropO Σ := λ v, match v with
    | None => True
    | Some l => ∃ (next : option loc), l ↦□ (option_loc_to_val next)%V ∗ ▷ F next
    end%I.

(* Ensures that the function used in the fixpoint combinator converges and is well-behaved.
   This means proving properties like contractiveness to guarantee that the recursive definition is sound, terminates correctly, and is suitable for use in formal proofs and reasoning. 
*)
Local Instance is_list_contr : Contractive (is_list_pre).
Proof. solve_contractive. Qed.

Definition is_list_def := fixpoint (is_list_pre).
Definition is_list_aux : seal (@is_list_def). Proof. by eexists. Qed.
Definition is_list := unseal (is_list_aux).

Definition kmem_inv v :=
  (∃ l ol', ⌜v = #l⌝ ∗ l ↦ option_loc_to_val ol' ∗ is_list ol')%I.

(*
  inv is a construct in the Iris framework used to define invariants.
  N is a namespace for the invariant. Namespaces in Iris help manage and categorize invariants to avoid conflicts and ensure proper scoping.

  is_kmem: Creates an invariant for the value v using the predicate kmem_inv.
  Invariants in Iris: Ensure that certain properties hold true for a value throughout the execution of the program.
  kmem_inv: Describes the properties that the value v must satisfy, which involve being a location that points to the head of a linked list.

*)
Definition is_kmem hd :=
  inv N (kmem_inv hd).

Definition is_list_eq : @is_list = @is_list_def := seal_eq (is_list_aux).

Lemma is_list_unfold v :
  is_list v ⊣⊢ is_list_pre (is_list) v.
Proof.
  rewrite is_list_eq. apply (fixpoint_unfold (is_list_pre)).
Qed.


Theorem new_kmem_spec :
  {{{ True }}} new_kmem #() {{{ s, RET s; is_kmem s }}}.
  Proof.
    iIntros (ϕ) "_ Hpost".
    wp_lam.
    wp_alloc ℓ as "Hl".
    iMod (inv_alloc N ⊤ (kmem_inv #ℓ) with "[Hl]") as "Hinv".
    { iNext; iExists ℓ, None; iFrame;
      by iSplit; last (iApply is_list_unfold). }
    by iApply "Hpost".
  Qed.

Theorem kfree_spec hd :
  {{{ is_kmem hd }}} kfree_rep hd {{{ RET #(); True }}}.
  Proof.
    iStartProof.
    Admitted.


Lemma is_list_dup v :
  is_list v -∗ is_list v ∗ match v with
  | None => True
  | Some l => ∃ t, l ↦□ (option_loc_to_val t)%V
  end.
  Proof.
    iIntros "Hkmem". iDestruct (is_list_unfold with "Hkmem") as "Hkmem".
    destruct v as [l|].
    - iDestruct "Hkmem" as (next) "(#Hl & ?)".
      rewrite (is_list_unfold (Some _)). iSplitL; iExists _; by iFrame.
    - rewrite is_list_unfold; iSplitR; eauto.
  Qed.

Theorem kalloc_spec hd :
  {{{ is_kmem hd }}} kalloc_rep hd {{{ ov, RET ov; ⌜ov = NONEV⌝ ∨ ∃ v, ⌜ov = SOMEV v⌝  }}}.
  Proof.
    iIntros (Φ) "#Hkmem HΦ".
    iLöb as "IH".
    wp_lam. wp_bind (Load _).
    iInv N as (ℓ v') "(>% & Hl & Hlist)" "Hclose"; subst.
    iDestruct (is_list_dup with "Hlist") as "[Hlist Hlist2]".
    wp_load.
    iMod ("Hclose" with "[Hl Hlist]") as "_".
    { iNext; iExists _, _; by iFrame. }
    iModIntro.
    destruct v' as [l|]; last first.
    - wp_match.
      iApply "HΦ"; by iLeft.
    - wp_match. wp_bind (Load _).
      iInv N as (ℓ' v') "(>% & Hl' & Hlist)" "Hclose". simplify_eq.
      iDestruct "Hlist2" as (?) "Hl".
      wp_load.
      iMod ("Hclose" with "[Hl' Hlist]") as "_".
      { iNext; iExists _, _; by iFrame. }
      iModIntro.
      wp_pures. wp_bind (CmpXchg _ _ _).
      iInv N as (ℓ'' v'') "(>% & Hl' & Hlist)" "Hclose". simplify_eq.
      destruct (decide (v'' = (Some l))) as [-> |].
      * rewrite is_list_unfold.
        iDestruct "Hlist" as (t') "(Hl'' & Hlist) /=".
        wp_cmpxchg_suc.
        iDestruct (pointsto_agree with "Hl'' Hl") as %[= <-%option_loc_to_val_inj].
        iMod ("Hclose" with "[Hl' Hlist]") as "_".
        { iNext; iExists ℓ'', _; by iFrame. }
        iModIntro.
        wp_pures.
         
        wp_bind (memset _ _ _). (* Set up the symbolic execution for memset. *)
        wp_rec.
        wp_let. wp_let. 
        wp_pures.
        
        
     (*   iModIntro.
        wp_store.
        
        wp_seq.
      
        iApply ("HΦ" with "[HP]"); iRight; iExists _; by iFrame.
      * wp_cmpxchg_fail. { destruct v''; simpl; congruence. }
        iMod ("Hclose" with "[Hl' Hlist]") as "_".
        { iNext; iExists ℓ'', _; by iFrame. }
        iModIntro.
        wp_pures.
        iApply ("IH" with "HΦ").*)
  Admitted.
End freelist.

Program Definition spec {Σ} N `{heapGS Σ} : concurrent_bag Σ :=
  {| is_bag := is_kmem N; new_bag := new_kmem; bag_push := kfree_rep; bag_pop := kalloc_rep |} .
Solve Obligations of spec with eauto using pop_spec, push_spec, new_kmem_spec.


Program Definition spec {Σ} N `{heapGS Σ} : concurrent_bag Σ :=
  {| is_bag := is_kmem P N; new_bag := new_kmem; bag_push := kfree_rep; bag_pop := kalloc_rep |} .
Solve Obligations of spec with eauto using kalloc_spec, kfree_spec, new_kmem_spec.


(*
    P: A predicate (val → iProp Σ) on values (val), which specifies the properties that each element in the list should satisfy.
    F: A non-expansive function (option loc -d> iPropO Σ) that defines the predicate for the rest of the list (the tail).
    The function returns another non-expansive function (option loc -d> iPropO Σ) that takes an option loc and returns an Iris proposition (iPropO Σ).
*)

(* Define the is_list_pre function without head value *)
Definition is_list_pre_no_head (F : option loc -d> iPropO Σ) :  option loc -d> iPropO Σ := 
  λ v, match v with
  | None => True
  | Some l => ∃ (t : option loc), l ↦□ (option_loc_to_val t)%V ∗ ▷ F t
  end%I.



(*

Definition is_list_pre (P : val → iProp Σ) (F : option loc -d> iPropO Σ) : option loc -d> iPropO Σ := 
λ v, match v with
| None => True
| Some l => ∃ (h : val) (t : option loc), l ↦□ (h, option_loc_to_val t)%V ∗ P h ∗ ▷ F t
end%I.


*)

(* Definition of the is_list_pre function *)
Definition is_list_pre (P : val → iProp Σ) (F : option loc -d> iPropO Σ) :
  option loc -d> iPropO Σ :=
  λ v, match v with
  | None => True
  (* When the optional location is None, the predicate is simply True *)
  | Some l =>
    (* When the optional location is Some l, the predicate involves:
       - An existential quantifier over a head value (h) and a tail (t)
       - A points-to relation for the location l, containing the pair (h, t)
       - The predicate P applied to the head value h
       - A later modality (▷) applied to the predicate F for the tail t
    *)
    ∃ (t : option loc),
      l ↦□ (option_loc_to_val t)%V ∗ (* Persistent points-to relation *)
      P h ∗                          (* Predicate P applied to head value h *)
      ▷ F t                          (* Later modality applied to F for tail t *)
  end%I. (* %I indicates that this is an Iris proposition *)








(* API specification *)
