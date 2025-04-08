Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
(*Require Import malloc_lemmas.
Require Import malloc_sep.*)

(* THIS SHOULD CONTAIN ANY INTERNAL FUNCTIONS... I DON'T HAVE ANY *)


(** token -- could be moved to another file *)

Definition my_kalloc_token (sh: share) (sz: Z) (p: val) : mpred := (* my kalloc token is a block where we can have t_run struct in it, but also something else?*)
  EX v,
    !! (
        field_compatible t_run [] p 
        /\ malloc_compatible (sz) p
        /\ 0 <= sizeof t_run <= sz
        /\ writable_share sh) 
  && ((memory_block sh (sz) (p)) * data_at sh t_run v p). (* this is the rest of the page*)

  

(** **** Exercise: 2 stars, standard (malloc_token_properties) *)
Lemma my_kalloc_token_valid_pointer:
    forall (sh : share) (sz : Z) (p : val),
      my_kalloc_token sh sz p |-- valid_pointer p.
Proof.
  intros. 
    induction sz.
  - unfold my_kalloc_token. simpl. entailer!. entailer.
  - unfold my_kalloc_token. simpl. entailer!. entailer.
  - unfold my_kalloc_token. entailer!. entailer. 
Qed.

Lemma  my_kalloc_token_local_facts : 
   forall (sh : share) (sz : Z) (p : val),
     my_kalloc_token sh sz p |-- !! malloc_compatible sz p.
Proof.
  intros. 
  unfold my_kalloc_token. simpl. entailer.
Qed.

(** token -- could be moved to another file *)


Definition Tok_APD := Build_KallocTokenAPD my_kalloc_token my_kalloc_token_valid_pointer
   my_kalloc_token_local_facts.

Definition mem_mgr (gv: globals) : mpred := (* I am unsure how to access all these elements.. *)
EX sh: share, EX ls: list val, EX xx, EX original_freelist_pointer,
    !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) *
      freelistrep sh ls original_freelist_pointer.

(************ mem_mgr lemmas etc. *************)
Lemma mem_mgr_split: 
 forall gv:globals,
  mem_mgr gv
  = 
  EX sh: share, EX ls: list val, EX xx, EX original_freelist_pointer,
      !! (writable_share sh /\
          is_pointer_or_null original_freelist_pointer /\
          (((ls = nil) /\ original_freelist_pointer = nullval) \/ ((ls <> nil) /\ isptr original_freelist_pointer))) &&
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) *
        freelistrep sh ls original_freelist_pointer.
Proof.
  intros. apply pred_ext.
  - unfold mem_mgr. Intros sh ls xx original_freelist_pointer. entailer!.
  Exists sh ls xx original_freelist_pointer. entailer!.
  - Intros sh ls xx original_freelist_pointer.
  unfold mem_mgr. Exists sh ls xx original_freelist_pointer. entailer!.
Qed.


Lemma kalloc_token'_split: 
 forall  (sh: share) (sz: Z) (p: val),
 my_kalloc_token  (sh) (sz) (p)
  = 
  EX v,
    !! (
        field_compatible t_run [] p 
        /\ malloc_compatible (sz) p
        /\ 0 <= sizeof t_run <= sz
        /\ writable_share sh) 
  && ((memory_block sh (sz) (p)) * data_at sh t_run v p). 
Proof.
  intros. apply pred_ext.
  - unfold my_kalloc_token. entailer!. Exists v. entailer!.
  - unfold my_kalloc_token. entailer!. Exists v. entailer!.
Qed.



(************ mem_mgr lemmas etc. end *************)





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

