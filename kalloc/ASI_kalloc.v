(** ** Abstract Specification Interface (ASI) *)

Require Import VST.floyd.proofauto.
Require Import VC.tactics.

(* ================================================================= *)
(** ** Abstract Predicate Declaration (APD) *)

Record KallocTokenAPD := {
  kalloc_token': share -> Z -> val -> mpred;
  kalloc_token'_valid_pointer: forall sh sz p, 
  kalloc_token' sh sz p |-- valid_pointer p;
  kalloc_token'_local_facts:  forall sh sz p, 
      kalloc_token' sh sz p |-- !! malloc_compatible sz p;
}.

Record KallocFreeAPD := {
  KF_Tok :> KallocTokenAPD;   (* whenever KallocFreeAPD is used, but a KallocTokenAPD is expected, it is automatically converted *)
  mem_mgr: globals -> mpred;
  mem_mgr_local_facts: forall gv,
    (mem_mgr gv) |-- (EX (sh : share), EX (ls: list val), EX (original_freelist_pointer:val), (* I am unsure how to access all these elements.. *)
      !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ))

}.

#[export] Hint Resolve kalloc_token'_valid_pointer : valid_pointer. 
#[export] Hint Resolve kalloc_token'_local_facts : saturate_local.

(* ================================================================= *)
(** ** Abstract Specification Interface (ASI) *)

Section Kalloc_ASI.
Variable K: KallocFreeAPD.
Variable kallocID: ident.
Variable kfreeID: ident.

Definition kfree_spec' := 
  DECLARE kfreeID
      WITH n:Z, new_head:val, gv:globals, sh:share
      PRE [ tptr tvoid]
        PROP(
              is_pointer_or_null new_head
              ) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
          mem_mgr K gv;
          if eq_dec new_head nullval then emp
          else (kalloc_token' K sh (n) new_head (* memory_block Ews n new_head*))
        )
      POST [ tvoid ]
        PROP()
        RETURN () 
        SEP (
          if eq_dec new_head nullval then 
          mem_mgr K gv
          else 
            mem_mgr K gv
            ).


Definition kalloc_spec' :=
DECLARE kallocID
WITH n:Z, gv:globals, sh:share
PRE [ ]
    PROP(0 <= n <= PGSIZE) 
    PARAMS () GLOBALS(gv)
    SEP ( mem_mgr K gv )  
POST [ tptr tvoid ] EX p:_,
    PROP()
    RETURN (p) 
    SEP (
      if (eq_dec p nullval) then
        (mem_mgr K gv * emp)
      else 
        kalloc_token' K sh n p *
        mem_mgr K gv
    ).

Definition Kalloc_ASI:funspecs := [kalloc_spec'; kfree_spec'].

End Kalloc_ASI.


