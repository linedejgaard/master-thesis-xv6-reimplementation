
(* ################################################################# *)
(** * The normal boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VC.client1.
Require Import VC.Specs_only.
Require Import VC.helper.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(** As usual, we define representation relations.  First, for the free list,
    which is just a linked list much as in [VSU_stack].*)

Definition t_run := Tstruct _run noattr.


(************************ freelistrep *********************************)
Fixpoint freelistrep (sh: share) (n: nat) (p: val) : mpred :=
 match n with
 | S n' => EX next: val, 
        !! malloc_compatible (sizeof t_run) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        data_at sh t_run next p * (* at the location p, there is a t_run structure with the value next *)
        freelistrep sh n' next (* "*" ensures no loops... *)
 | O => !! (p = nullval) && emp
 end.

Arguments freelistrep sh n p : simpl never.

Lemma freelistrep_local_prop: forall sh n p, 
   freelistrep sh n p |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
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
  forall sh n p, 
  readable_share sh ->
   freelistrep sh n p |-- valid_pointer p.
Proof.
  intros. destruct n.
  - unfold freelistrep. entailer!.
  - unfold freelistrep. Intro y; entailer.
Qed. 
#[export] Hint Resolve freelistrep_valid_pointer : valid_pointer.


Lemma freelistrep_null: forall sh n x,
       x = nullval ->
       freelistrep sh n x = !! (n = O) && emp.
Proof.
   intros.
   destruct n; unfold freelistrep; fold freelistrep.
   autorewrite with norm. auto.
   apply pred_ext.
   Intros y. entailer. 
   destruct n; entailer!; try discriminate H0. 
Qed.

Lemma freelistrep_nonnull: forall n sh x,
   x <> nullval ->
   freelistrep sh n x =
   EX m : nat, EX next:val,
          !! (n = S m) && !! malloc_compatible (sizeof t_run) x && data_at sh t_run next x * freelistrep sh m next.
Proof.
   intros; apply pred_ext.
   - destruct n. 
         + unfold freelistrep. entailer!.
         + unfold freelistrep; fold freelistrep. Intros y.
         Exists n y. entailer!.
   - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. Exists y. entailer!.
Qed.


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
   sizeof(t_run), which  is ?? bytes when [sizeof(size_t)=4] or 
   32 bytes when [sizeof(size_t)=8].  When [malloc(7)] splits a
   block into two pieces, the malloc_token represents the
   second piece, the portion of the block between offset 7 and the end.
   That is the [memory_block] shown in the definition below.
  - In addition, the malloc_token has three propositional facts about
   address [p], that will assist the [free()] function in reconstituting
   the two parts of the split block. *)
 
Definition malloc_token_sz (sh: share) (n: Z) (p: val) : mpred := 
  !! (field_compatible t_run [] p 
      /\ malloc_compatible (sizeof t_run) p
      /\ 0 <= n <= sizeof t_run) 
 &&  memory_block Ews (sizeof t_run - n) (offset_val n p).

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

(** The next three lines define an opaque constant that, nevertheless,
  rep_lia can unfold.     See VC.pdf, chapter 65 "Opaque Constants". *)
Definition N : Z := proj1_sig (opaque_constant 80000).
Definition N_eq : N=_ := proj2_sig (opaque_constant _).
#[export] Hint Rewrite N_eq : rep_lia.



(* ################################################################# *)
(** * Defining the mem_mgr APD *)

(** This [mem_mgr] predicate is the client-view abstract predicate
  that characterizes the contents of this module's global state variables,
  [pool], [pool_index], and [freelist]. *)

Definition mem_mgr (gv: globals) : mpred :=
    EX sh:share, EX head:val, EX xx:Z, EX n:nat,
    data_at sh t_struct_kmem (Vint (Int.repr xx), head) (gv _kmem) *
    freelistrep sh n head.


Definition M : MallocFreeAPD := 
    Build_MallocFreeAPD mem_mgr malloc_token_sz
           malloc_token_sz_valid_pointer malloc_token_sz_local_facts.

(* ################################################################# *)
(** * Constructing Vprog and Gprog *)

  Definition MF_ASI: funspecs := MallocFreeASI M.
  Definition MF_imported_specs:funspecs :=  nil.
  Definition MF_internal_specs: funspecs := MF_ASI.
  Definition MF_globals gv : mpred:= Specs_only.mem_mgr M gv.
  Definition MFVprog : varspecs. mk_varspecs client1.prog. Defined.
  Definition MFGprog: funspecs := MF_imported_specs ++ MF_internal_specs.

(** **** Exercise: 3 stars, standard (stdlib2_body_malloc) *)

Lemma body_kalloc: semax_body MFVprog MFGprog f_kalloc1 (kalloc_spec_sz M).
Proof.
  start_function.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (stdlib2_body_free) *)
Lemma body_free: semax_body MFVprog MFGprog f_kfree1 (kfree_spec_sz M).
(* FILL IN HERE *) Admitted.
(** [] *)

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

  (*Definition MF_Externs : funspecs := nil.

Definition MallocFreeVSU: @VSU NullExtension.Espec
         MF_Externs MF_imported_specs ltac:(QPprog prog) MF_ASI MF_globals.
  Proof. 
    mkVSU prog MF_internal_specs.
    - solve_SF_internal body_malloc.
    - solve_SF_internal body_free.
    - solve_SF_internal body_exit.
    - apply initialize; auto.
Qed.*)

(* ================================================================= *)
(** ** Next Chapter: [VSU_main2] *)

(* 2023-03-25 11:30 *)
