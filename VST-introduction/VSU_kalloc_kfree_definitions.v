Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
(*Require Import malloc_lemmas.
Require Import malloc_sep.*)

(* THIS SHOULD CONTAIN ANY INTERNAL FUNCTIONS... I DON'T HAVE ANY *)


(** token -- could be moved to another file *)

Definition my_kalloc_token (sh: share) (sz: Z) (p: val) (t:type) : mpred := (* my kalloc token is a block where we can have t_run struct in it, but also something else?*)
  EX v,
    !! (
        field_compatible t [] p 
        /\ malloc_compatible sz p
        /\ 0 <= sizeof t <= sz
        /\ writable_share sh) 
  && (((*memory_block sh (sz) (p *) (data_at sh t v p))). (* this is the rest of the page*)
  

(** **** Exercise: 2 stars, standard (malloc_token_properties) *)
Lemma my_kalloc_token_valid_pointer:
    forall (sh : share) (sz : Z) (p : val) (t: type),
    0 < sizeof t ->
    readable_share sh ->
      my_kalloc_token sh sz p t |-- valid_pointer p.
Proof.
  intros.
  unfold my_kalloc_token. entailer!.
  apply data_at_valid_ptr; try rep_lia; auto.
Qed.

Lemma  my_kalloc_token_local_facts : 
   forall (sh : share) (sz : Z) (p : val) (t:type),
     my_kalloc_token sh sz p t |-- !! malloc_compatible sz p.
Proof.
  intros. 
  unfold my_kalloc_token. simpl. entailer.
Qed.

(** token -- could be moved to another file *)


Definition Tok_APD := Build_KallocTokenAPD my_kalloc_token my_kalloc_token_valid_pointer
   my_kalloc_token_local_facts.

Definition mem_mgr (gv: globals) (sh : share) (ls: list val) (xx:Z) (original_freelist_pointer:val): mpred := (* I am unsure how to access all these elements.. *)
    !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).

(************ mem_mgr lemmas etc. *************)
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


Lemma kalloc_token'_split: 
 forall  (sh: share) (sz: Z) (p: val) (t:type),
 my_kalloc_token  (sh) (sz) (p) (t)
  = 
  EX v,
    !! (
        field_compatible t [] p 
        /\ malloc_compatible sz p
        /\ 0 <= sizeof t <= sz
        /\ writable_share sh) 
  && (((*memory_block sh (sz) (p *) (data_at sh t v p))).
Proof.
  intros. apply pred_ext.
  - unfold my_kalloc_token. entailer. entailer!. Exists v. entailer!.
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

