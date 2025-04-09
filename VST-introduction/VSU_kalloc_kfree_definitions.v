Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
(*Require Import malloc_lemmas.
Require Import malloc_sep.*)

(* THIS SHOULD CONTAIN ANY INTERNAL FUNCTIONS... I DON'T HAVE ANY *)


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
(***** kalloc token size ******)


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

