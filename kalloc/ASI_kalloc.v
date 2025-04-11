(** abstract spec interface *)
Require Import VST.floyd.proofauto.
Require Import VC.tactics.

(*Global Open Scope funspec_scope.*)

Record KallocTokenAPD := {
  kalloc_token': share -> Z -> val -> mpred;
  kalloc_token'_valid_pointer: forall sh sz p, 
  kalloc_token' sh sz p |-- valid_pointer p;
  kalloc_token'_local_facts:  forall sh sz p, 
      kalloc_token' sh sz p |-- (!! (
            0 < sz <= PGSIZE
            /\ malloc_compatible (sz) p 
            /\ malloc_compatible (PGSIZE) p
            /\ writable_share sh
            /\ malloc_compatible sz p) && memory_block sh (sz) (p));
}.

Record KallocFreeAPD := {
  MF_Tok :> KallocTokenAPD;
  mem_mgr: globals -> share -> list val -> Z -> val -> mpred;
}.

#[export] Hint Resolve kalloc_token'_valid_pointer : valid_pointer. 
#[export] Hint Resolve kalloc_token'_local_facts : saturate_local.

Section Kalloc_ASI.
Variable K: KallocFreeAPD.
Variable kallocID: ident.
Variable kfreeID: ident.
Variable kfreeLoopID: ident.

Definition kfree_spec' := 
  DECLARE kfreeID
      WITH n:Z, new_head:val, gv:globals, sh:share, ls: list val, xx:Z, original_freelist_pointer:val
      PRE [ tptr tvoid]
        PROP(
              is_pointer_or_null new_head
              ) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
          mem_mgr K gv sh ls xx original_freelist_pointer;
          if eq_dec new_head nullval then emp
          else (kalloc_token' K sh (n) new_head (* memory_block Ews n new_head*))
        )
      POST [ tvoid ]
        PROP()
        RETURN () 
        SEP (
          if eq_dec new_head nullval then 
          mem_mgr K gv sh ls xx original_freelist_pointer
          else 
            mem_mgr K gv sh (original_freelist_pointer::ls) xx new_head
            ).


Definition kalloc_spec' :=
DECLARE kallocID
WITH n:Z, gv:globals, sh:share, ls: list val, xx:Z, original_freelist_pointer:val
PRE [ ]
    PROP(0 <= n <= PGSIZE) 
    PARAMS () GLOBALS(gv)
    SEP ( mem_mgr K gv sh ls xx original_freelist_pointer )  
POST [ tptr tvoid ]
    PROP()
    RETURN (original_freelist_pointer) 
    SEP (
      if (eq_dec original_freelist_pointer nullval) then
        (mem_mgr K gv sh ls xx original_freelist_pointer * emp)
      else 
        (
          EX next ls',
          (!! (next :: ls' = ls) &&
              kalloc_token' K sh n original_freelist_pointer *
              mem_mgr K gv sh ls' xx next
          )
        )
    ).


Definition Kalloc_ASI:funspecs := [kalloc_spec'; kfree_spec'].

End Kalloc_ASI.


