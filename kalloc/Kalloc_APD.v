Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.ASI_kalloc.



(* ================================================================= *)
(** ** Defining APD: use tokens based on size *)

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

Definition KAF_APD := Build_KallocFreeAPD Tok_APD mem_mgr.

(* ================================================================= *)
(** ** Constructing Vprog and Gprog *)

Definition KAF_ASI: funspecs := Kalloc_ASI KAF_APD _kalloc _kfree.
Definition KAF_internal_specs: funspecs := KAF_ASI.
Definition KAF_globals gv  sh ls xx original_freelist_pointer: mpred:= ASI_kalloc.mem_mgr KAF_APD gv sh ls xx original_freelist_pointer.
Definition KAFVprog : varspecs. mk_varspecs kalloc.prog. Defined.
Definition KAFGprog: funspecs := KAF_internal_specs.

(* ================================================================= *)
(** ** Lemma to unfold mem_mgr *)

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

Ltac start_function_hint ::= idtac. (* no hint reminder *)

