Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
(*Require Import malloc_lemmas.
Require Import malloc_sep.*)

(* THIS SHOULD CONTAIN ANY INTERNAL FUNCTIONS... I DON'T HAVE ANY *)


Definition my_kalloc_token (sh: share) (sz: Z) (p: val) : mpred := (* my kalloc token is a block where we can have t_run struct in it, but also something else?*)
  !! (field_compatible t_run [] p 
      /\ malloc_compatible (sz) p
      /\ 0 <= sizeof t_run <= sz
      /\ writable_share sh) 
 &&  memory_block sh (sz) (p). (* this is the rest of the page*)

(** **** Exercise: 2 stars, standard (malloc_token_properties) *)
Lemma my_kalloc_token_valid_pointer:
    forall (sh : share) (sz : Z) (p : val),
      my_kalloc_token sh sz p |-- valid_pointer p.
Proof.
  intros. 
    induction sz.
  - unfold my_kalloc_token. simpl. entailer!.
  - unfold my_kalloc_token. simpl. entailer!.
  - unfold my_kalloc_token. entailer!. 
Qed.

Lemma  my_kalloc_token_local_facts : 
   forall (sh : share) (sz : Z) (p : val),
     my_kalloc_token sh sz p |-- !! malloc_compatible sz p.
Proof.
  intros. 
  unfold my_kalloc_token. simpl. entailer!.
Qed.

Definition Tok_APD := Build_KallocTokenAPD my_kalloc_token my_kalloc_token_valid_pointer
   my_kalloc_token_local_facts.

Definition mem_mgr (gv: globals) : mpred :=
   EX sh: share, EX i: Z, EX p: val, EX ls: list val, EX xx, EX original_freelist_pointer,
      data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) *
      freelistrep sh ls original_freelist_pointer.

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