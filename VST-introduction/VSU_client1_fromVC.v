
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
        !! malloc_compatible (PGSIZE) p &&  (* p is compatible with a memory block of size sizeof theader. *)
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
          !! (n = S m) && !! malloc_compatible (PGSIZE) x && data_at sh t_run next x * freelistrep sh m next.
Proof.
   intros; apply pred_ext.
   - destruct n. 
         + unfold freelistrep. entailer!.
         + unfold freelistrep; fold freelistrep. Intros y.
         Exists n y. entailer!.
   - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. Exists y. entailer!.
Qed.


(* ################################################################# *)
 
Definition malloc_token_sz (sh: share) (n: Z) (p: val) : mpred := 
  !! (field_compatible t_run [] p 
      /\ malloc_compatible (PGSIZE) p
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


(* ################################################################# *)
(** * Defining the mem_mgr APD *)

(** This [mem_mgr] predicate is the client-view abstract predicate
  that characterizes the contents of this module's global state variables,
  [pool], [pool_index], and [freelist]. *)

Definition mem_mgr (gv: globals) : mpred :=
    EX sh:share, EX head:val, EX xx:Z, EX n:nat,
    !! (is_pointer_or_null head) &&
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

(** **** Exercise: 3 stars, standard (stdlib2_body_free) *)
Lemma body_kfree: semax_body MFVprog MFGprog f_kfree1 (kfree_spec_sz M).
Proof.
  start_function.
  destruct (eq_dec p nullval).
  - forward.
(* FILL IN HERE *) Admitted.

Lemma body_kalloc: semax_body MFVprog MFGprog f_kalloc1 (kalloc_spec_sz M).
Proof.
  start_function.
(* FILL IN HERE *) Admitted.
(** [] *)



