(** abstract spec interface *)
Require Import VST.floyd.proofauto.
Require Import VC.helper.

Global Open Scope funspec_scope.

Record KallocTokenAPD := {
  kalloc_token': share -> Z -> val -> mpred;
  kalloc_token'_valid_pointer: forall sh sz p, 
      kalloc_token' sh sz p |-- valid_pointer p;
  kalloc_token'_local_facts:  forall sh sz p, 
      kalloc_token' sh sz p |-- !! malloc_compatible sz p;
}.

Record KallocFreeAPD := {
  MF_Tok :> KallocTokenAPD;
  mem_mgr: globals -> mpred;
}.

#[export] Hint Resolve kalloc_token'_valid_pointer : valid_pointer. 

#[export] Hint Resolve kalloc_token'_local_facts : saturate_local.

Section Kalloc_ASI.
Variable K: KallocFreeAPD.
Variable kalloc1ID: ident.
Variable kfree1ID: ident.


Definition kfree1_spec := 
  DECLARE kfree1ID
      WITH t:type, new_head:val, gv:globals 
      PRE [ tptr tvoid]
        PROP(
              is_pointer_or_null new_head
              ) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
          mem_mgr K gv;
          if eq_dec new_head nullval then emp
          else (kalloc_token' K Ews (sizeof t) new_head * data_at_ Ews t new_head)
        )
      POST [ tvoid ]
        PROP()
        RETURN () 
        SEP (
          mem_mgr K gv
            ).


Definition kalloc1_spec :=
DECLARE kalloc1ID
WITH t:type, gv:globals 
PRE [ ]
    PROP(0 <= sizeof t <= PGSIZE;
    complete_legal_cosu_type t = true;
    natural_aligned natural_alignment t = true) 
    PARAMS () GLOBALS(gv)
    SEP ( mem_mgr K gv )  
POST [ tptr tvoid ]
  EX p:val,
    PROP()
    RETURN (p) 
    SEP (
      mem_mgr K gv;
      if eq_dec p nullval then emp
      else (kalloc_token' K Ews (sizeof t) p * data_at_ Ews t p) (** TODO: fix EWs...*)
        ).

Definition Kalloc_ASI:funspecs := [kalloc1_spec; kfree1_spec].
End Kalloc_ASI.
        