Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
(*Require Import malloc_lemmas.
Require Import malloc_sep.*)

(* THIS SHOULD CONTAIN ANY INTERNAL FUNCTIONS... I DON'T HAVE ANY *)


(** token -- could be moved to another file *)
(*** kalloc token size... *)
(***** kalloc token size ******)
Definition kalloc_token_sz (sh: share) (n: Z) (p: val) : mpred :=
  !! ((*field_compatible t_run [] p /\*)
      0 < n <= PGSIZE
      /\ malloc_compatible (n) p 
      /\ malloc_compatible (PGSIZE) p
      /\ writable_share sh
      (*/\  maybe some alignment and physical address checks here *))
  && memory_block sh (n) (p).

Lemma kalloc_token_sz_valid_pointer:
  forall (sh : share) (sz : Z) (p : val),
  kalloc_token_sz sh sz p |-- valid_pointer p.
Proof.
  intros. 
  unfold kalloc_token_sz. entailer.
Qed.

Lemma  kalloc_token_sz_local_facts : 
 forall (sh : share) (n:Z) (p : val) ,
   kalloc_token_sz sh n p |-- !! malloc_compatible n p.
Proof.
  intros. 
  unfold kalloc_token_sz. simpl. entailer.
Qed.

(******************************)

(*** kalloc token type... *)
Definition my_kalloc_token {cs: compspecs} sh t p :=
  !! field_compatible t [] p && (* this shoudl work because of memory_block_data_at_*)
  (kalloc_token_sz sh (sizeof t) p).

Lemma my_kalloc_token_valid_pointer:
  forall (sh : share) (t : type) (p : val),
  my_kalloc_token sh t p |-- valid_pointer p.
Proof.
  intros. 
  unfold my_kalloc_token. unfold kalloc_token_sz. entailer!.
Qed.

Ltac kalloc_token_data_at_valid_pointer :=
  match goal with |- ?A |-- valid_pointer ?p =>
   match A with
   | context [my_kalloc_token _ _ ?t p] =>
         try (assert (sizeof t <= 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         try (assert (sizeof t > 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         destruct (zlt 0 (sizeof t));
         auto with valid_pointer
   | context [kalloc_token_sz _ _ ?n p] =>
         try (assert (n <= 0) by rep_lia; fail 1);
         try (assert (n > 0) by rep_lia; fail 1);
         destruct (zlt 0 n);
         auto with valid_pointer
   end
 end.

#[export] Hint Extern 1 (my_kalloc_token _ _ _ _ |-- valid_pointer _) =>
  (simple apply my_kalloc_token_valid_pointer; data_at_valid_aux) : valid_pointer.
#[export] Hint Extern 4 (_ |-- valid_pointer _) => kalloc_token_data_at_valid_pointer : valid_pointer.

Lemma my_kalloc_token_local_facts:  forall {cs: compspecs} sh t p,
      my_kalloc_token sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold my_kalloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply kalloc_token_sz_local_facts.
Qed.
#[export] Hint Resolve my_kalloc_token_local_facts : saturate_local.



Definition Tok_APD := Build_KallocTokenAPD kalloc_token_sz kalloc_token_sz_valid_pointer
  kalloc_token_sz_local_facts.


Definition mem_mgr (gv: globals) (sh : share) (ls: list val) (xx:Z) (original_freelist_pointer:val): mpred := (* I am unsure how to access all these elements.. *)
    !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).

(************ lemmas etc. *************)
Lemma mem_mgr_split: 
 forall (gv:globals) (sh:share) (ls: list val) (xx:Z) (original_freelist_pointer:val),
  mem_mgr gv sh ls xx original_freelist_pointer
  = 
  !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).
Proof.
  intros. apply pred_ext.
  - unfold mem_mgr. entailer!.
  - unfold mem_mgr. entailer!.
Qed.

Lemma kalloc_token_sz_split:
forall  (sh: share) (n: Z) (p: val),
  kalloc_token_sz sh n p =
  !! ((*field_compatible t_run [] p /\*)
  0 < n <= PGSIZE
  /\ malloc_compatible (n) p 
  /\ malloc_compatible (PGSIZE) p
  /\ writable_share sh
  (*/\  maybe some alignment and physical address checks here *))
  && memory_block sh (n) (p).
Proof.
  intros. apply pred_ext.
  - unfold kalloc_token_sz. entailer.
  - unfold kalloc_token_sz. entailer!.
Qed.

Lemma my_kalloc_token_split: 
 forall (sh: share) (t: type) (p: val),
 my_kalloc_token (sh) (t) (p)
  = 
  !! field_compatible t [] p &&
  (kalloc_token_sz sh (sizeof t) p).
Proof.
  intros. apply pred_ext.
  - unfold my_kalloc_token. entailer.
  - unfold my_kalloc_token. entailer!.
Qed.

(************ lemmas etc. end *************)


Definition KF_APD := Build_KallocFreeAPD Tok_APD mem_mgr.

(*+ specs of private functions *)


Definition MF_Vprog : varspecs. mk_varspecs prog. Defined.

Definition MF_internal_specs: funspecs :=
    [].
   (*++ _malloc _free.*)

(*Definition MF_Imports:funspecs := Mmap0_ASI _mmap0 _munmap.*)

Definition MF_Gprog:funspecs := (*MF_Imports ++*) MF_internal_specs.
(* I don't think I have any internal specs netiher MF imports..*)

Ltac start_function_hint ::= idtac. (* no hint reminder *)

