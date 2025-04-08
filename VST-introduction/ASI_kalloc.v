Require Import VST.floyd.proofauto.
Require Import VC.helper.
(*Require Export malloc_lemmas.*) (*Exports the model (constants like WA , plus lemmas)*)

(*Require Import malloc. needed for function and type names but not for compspecs 
Update: Some UPenn grad students proposed to abstract over function identifiers -
doing so in our setup makes ASIs source-program-independent!*)

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

(*Definition kalloc_token {cs:compspecs} K (sh: share) (t: type) (p: val): mpred := 
   !! field_compatible t [] p && 
   kalloc_token' K sh (sizeof t) p.

Lemma kalloc_token_valid_pointer: forall {cs: compspecs} K sh t p, 
      kalloc_token K sh t p |-- valid_pointer p.
Proof. intros. unfold kalloc_token.
 apply andp_left2. apply kalloc_token'_valid_pointer.
Qed.

*)#[export] Hint Resolve kalloc_token'_valid_pointer : valid_pointer. (*
#[export] Hint Resolve kalloc_token_valid_pointer : valid_pointer.

Lemma kalloc_token_local_facts:  forall {cs: compspecs} K sh t p,
      kalloc_token K sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold kalloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply kalloc_token'_local_facts.
Qed.*)

#[export] Hint Resolve kalloc_token'_local_facts : saturate_local.
(*#[export] Hint Resolve kalloc_token_local_facts : saturate_local.*)

Section Kalloc_ASI.
Variable K: KallocFreeAPD.
Variable kalloc1ID: ident.
Variable kfree1ID: ident.


Definition kfree1_spec := 
  DECLARE kfree1ID
      WITH t:type, new_head:val, gv:globals (*sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, size:Z, n:Z (* n = PGSIZE.. *)*)
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
WITH t:type, gv:globals (*sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals, n:Z*) (* n = PGSIZE.. *)
PRE [ ]
    PROP(0 <= sizeof t <= PGSIZE;
    complete_legal_cosu_type t = true;
    natural_aligned natural_alignment t = true) 
    PARAMS () GLOBALS(gv)
    SEP ( mem_mgr K gv )  
POST [ tptr tvoid ]
  EX p:val,
    PROP()
    RETURN (p) (* we return the head like in the pop function*)
    SEP (
      mem_mgr K gv;
      if eq_dec p nullval then emp
      else (kalloc_token' K Ews (sizeof t) p * data_at_ Ews t p) (** TODO: fix EWs...*)
        ).

Definition Kalloc_ASI:funspecs := [kalloc1_spec; kfree1_spec].
End Kalloc_ASI.
        