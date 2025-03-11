(** * VSU_stdlib2: Malloc/free/exit programmed in C *)

(** In contrast to [VSU_stdlib] which axiomatized malloc, free,
  and exit as external functions, in this chapter we construct them as
  ordinary C functions, and prove them correct.  This chapter shows
  how to manage global variables that are private to a module.

 In the C code, there is a [stdlib.h] interface, with alternative
 implementations [stdlib.c] and [stdlib2.c] that are quite
 independent of each other.

 The the proofs, there is a specification [Spec_stdlib.MallocFreeASI]
 (that is, the "malloc-free Abstract Specification Interface")
 with two alternative implementations-with-proofs,
 [VSU_stdlib.MallocFreeVSU] and [VSU_stdlib2.MallocFreeVSU].

 That second VSU is the one we build in this chapter.
*)

(* ################################################################# *)
(** * The C program *)

(*

#include "kernel/types.h"
#include "kernel/stat.h"
#include "user/user.h"
#include "kernel/param.h"

// Memory allocator by Kernighan and Ritchie,
// The C programming Language, 2nd ed.  Section 8.7.

typedef long Align;

union header {
  struct {
    union header *ptr;
    uint size;
  } s;
  Align x;
};

typedef union header Header;

static Header base;
static Header *freep;

void
free(void *ap)
{
  Header *bp, *p;

  bp = (Header* )ap - 1;
  for(p = freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)
    if(p >= p->s.ptr && (bp > p || bp < p->s.ptr))
      break;
  if(bp + bp->s.size == p->s.ptr){
    bp->s.size += p->s.ptr->s.size;
    bp->s.ptr = p->s.ptr->s.ptr;
  } else
    bp->s.ptr = p->s.ptr;
  if(p + p->s.size == bp){
    p->s.size += bp->s.size;
    p->s.ptr = bp->s.ptr;
  } else
    p->s.ptr = bp;
  freep = p;
}

static Header*
morecore(uint nu)
{
  char *p;
  Header *hp;

  if(nu < 4096)
    nu = 4096;
  p = sbrk(nu * sizeof(Header));
  if(p == (char* )-1)
    return 0;
  hp = (Header* )p;
  hp->s.size = nu;
  free((void* )(hp + 1));
  return freep;
}

void*
malloc(uint nbytes)
{
  Header *p, *prevp;
  uint nunits;

  nunits = (nbytes + sizeof(Header) - 1)/sizeof(Header) + 1;
  if((prevp = freep) == 0){
    base.s.ptr = freep = prevp = &base;
    base.s.size = 0;
  }
  for(p = prevp->s.ptr; ; prevp = p, p = p->s.ptr){
    if(p->s.size >= nunits){
      if(p->s.size == nunits)
        prevp->s.ptr = p->s.ptr;
      else {
        p->s.size -= nunits;
        p += p->s.size;
        p->s.size = nunits;
      }
      freep = prevp;
      return (void* )(p + 1);
    }
    if(p == freep)
      if((p = morecore(nunits)) == 0)
        return 0;
  }
}
*)


 
(* ################################################################# *)
(** * The normal boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VC.umalloc.
Require Import VC.Spec_umalloc.
#[export] Instance CompSpecs : compspecs. make_compspecs umalloc.prog. Defined.

(** As usual, we define representation relations.  First, for the free list,
    which is just a linked list much as in [VSU_stack].*)

Definition theader := Tunion _header noattr.
(* Compute (reptype theader). *)


Fixpoint freelistrep (n: nat) (p: val) : mpred :=
 match n with
 | S n' => EX next: val, 
        !! malloc_compatible (sizeof theader) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        data_at Ews theader (inl (next, Vundef)) p * (* at the location p, there is a theader structure with the value inl (y, Vundef). inl and inr are constructors for the sum type (+) in Coq. They are used to distinguish between the two possible cases in a sum type. Use inl to get the left value, use inr to get the right value *)
        freelistrep n' next
 | O => !! (p = nullval) && emp
 end.

Arguments freelistrep n p : simpl never.

Lemma freelistrep_local_prop: forall n p, 
   freelistrep n p |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros.
  induction n as [| n' IH].
  - unfold freelistrep. entailer!. split; auto.
    + split; auto.
    + split; try lia. intros. simpl in *. inversion H.
  - unfold freelistrep. destruct p; Intro y; entailer!. split.
    + split; intros; inversion H2.
    + split; intros; auto. try lia. 
   Qed.
#[export] Hint Resolve freelistrep_local_prop : saturate_local.

Lemma freelistrep_valid_pointer:
  forall n p,
   freelistrep n p |-- valid_pointer p.
Proof.
  intros. destruct n.
  - unfold freelistrep. entailer!.
  - unfold freelistrep. Intro y; entailer.
Qed.
#[export] Hint Resolve freelistrep_valid_pointer : valid_pointer.
(** [] *)

(* ################################################################# *)
(** * malloc_token *)

(** Suppose the user does [p = malloc(7);].  Then [p] points to
  a newly allocated block of 7 bytes.  What does [malloc_token(p)]
  represent?
  - Normally, there must be some way for [free(p)] to figure out
   the size of the block.  This can be done by having a header word,
   just before address p, that gives the size (though there are other
   ways to do it).  Normally, this header word is part of what 
   malloc_token represents.  But in this implementation, all blocks
   are the same size, so there's no need for such a header.
  - The memory-manager's free list contains blocks all of size
   sizeof(tcell), which  is 16 bytes when [sizeof(size_t)=4] or 
   32 bytes when [sizeof(size_t)=8].  When [malloc(7)] splits a
   block into two pieces, the malloc_token represents the
   second piece, the portion of the block between offset 7 and the end.
   That is the [memory_block] shown in the definition below.
  - In addition, the malloc_token has three propositional facts about
   address [p], that will assist the [free()] function in reconstituting
   the two parts of the split block. *)
 
Definition malloc_token_sz (sh: share) (n: Z) (p: val) : mpred := 
  !! (field_compatible theader [] p 
      /\ malloc_compatible (sizeof theader) p
      /\ 0 <= n <= sizeof theader) 
 &&  memory_block Ews (sizeof theader - n) (offset_val n p).

(** **** Exercise: 2 stars, standard (malloc_token_properties) *)
Lemma malloc_token_sz_valid_pointer:
    forall (sh : share) (sz : Z)  (p : val),
            sz <= 0 ->
              malloc_token_sz sh sz p |-- valid_pointer p.
Proof.
  intros. 
  induction sz.
  - unfold malloc_token_sz. simpl. entailer!.
  - unfold malloc_token_sz. simpl. entailer!.
  - unfold malloc_token_sz. entailer!. inversion H2. 
    assert (0 = Z.neg p0). { try lia. }
    inversion H7.
Qed.

Lemma  malloc_token_sz_local_facts : 
   forall (sh : share) (sz : Z) (p : val),
     malloc_token_sz sh sz p |-- !! malloc_compatible sz p.
Proof.
  intros. 
  unfold malloc_token_sz. simpl. entailer!.
  unfold malloc_compatible in *. destruct p; simpl; auto. split; destruct H0; auto. 
    try lia.
Qed. 
(** [] *)

(* ################################################################# *)
(** * Defining the mem_mgr APD *)

(** This [mem_mgr] predicate is the client-view abstract predicate
  that characterizes the contents of this module's global state variables,
  [pool], [pool_index], and [freelist]. *)

Definition mem_mgr (gv: globals) : mpred :=
 EX i: Z, EX p: val, EX frees: nat,
  !! (0 <= i <= N) &&
  data_at Ews tint (Vint (Int.repr i)) (gv _pool_index) *
  data_at_ Ews (tarray tcell (N-i))
     (field_address0 (tarray tcell N) [ArraySubsc i]  (gv _pool)) *
  data_at Ews (tptr tcell) p (gv _freelist) *
  freelistrep frees p.

Definition M : MallocFreeAPD := 
    Build_MallocFreeAPD mem_mgr malloc_token_sz
           malloc_token_sz_valid_pointer malloc_token_sz_local_facts.

(* ################################################################# *)
(** * Constructing Vprog and Gprog *)

  Definition MF_ASI: funspecs := MallocFreeASI M.
  Definition MF_imported_specs:funspecs :=  nil.
  Definition MF_internal_specs: funspecs := MF_ASI.
  Definition MF_globals gv : mpred:= Spec_stdlib.mem_mgr M gv.
  Definition MFVprog : varspecs. mk_varspecs stdlib2.prog. Defined.
  Definition MFGprog: funspecs := MF_imported_specs ++ MF_internal_specs.

(** **** Exercise: 3 stars, standard (stdlib2_body_malloc) *)

Lemma body_malloc: semax_body MFVprog MFGprog f_malloc (malloc_spec_sz M).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (stdlib2_body_free) *)
Lemma body_free: semax_body MFVprog MFGprog f_free (free_spec_sz M).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (stdlib2_body_exit) *)
Lemma body_exit: semax_body MFVprog MFGprog f_exit exit_spec.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Initializers for global data *)

Check @Comp_MkInitPred.
(**  Each VSU may have private global variables that constitute its
  "local state".  The client of the VSU should not access these
  directly; and in separation logic all these variables should be
  abstracted as a single abstract predicate.  Since these variables
  may have initial values that concretely represent some abstract
  state, we need an axiom in the VSU interface (proved as a lemma
  in the VSU implementation), saying that the initial values
  properly represent a proper state of the abstract predicate. *)

(** **** Exercise: 2 stars, standard (stdlib2_initialize) *)
Lemma initialize: VSU_initializer prog MF_globals.
Proof.
InitGPred_tac.
unfold MF_globals.
(* FILL IN HERE *) Admitted.

(* ================================================================= *)
(** ** Defining the pieces of a VSU

    And now, in the usual way, we can put totether the pieces: *)

(* ################################################################# *)
(** * Constructing the Component and the VSU *)

  Definition MF_Externs : funspecs := nil.

Definition MallocFreeVSU: @VSU NullExtension.Espec
         MF_Externs MF_imported_specs ltac:(QPprog prog) MF_ASI MF_globals.
  Proof. 
 mkVSU prog MF_internal_specs.
    - solve_SF_internal body_malloc.
    - solve_SF_internal body_free.
    - solve_SF_internal body_exit.
    - apply initialize; auto.
Qed.

(* ================================================================= *)
(** ** Next Chapter: [VSU_main2] *)

(* 2023-03-25 11:30 *)
