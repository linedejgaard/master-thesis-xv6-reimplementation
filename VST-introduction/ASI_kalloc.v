Require Import VST.floyd.proofauto.
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

Definition kalloc_token {cs:compspecs} K (sh: share) (t: type) (p: val): mpred := 
   !! field_compatible t [] p && 
   kalloc_token' K sh (sizeof t) p.

Lemma kalloc_token_valid_pointer: forall {cs: compspecs} K sh t p, 
      kalloc_token K sh t p |-- valid_pointer p.
Proof. intros. unfold kalloc_token.
 apply andp_left2. apply kalloc_token'_valid_pointer.
Qed.

#[export] Hint Resolve kalloc_token'_valid_pointer : valid_pointer.
#[export] Hint Resolve kalloc_token_valid_pointer : valid_pointer.

Lemma kalloc_token_local_facts:  forall {cs: compspecs} K sh t p,
      kalloc_token K sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold kalloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply kalloc_token'_local_facts.
Qed.

#[export] Hint Resolve kalloc_token'_local_facts : saturate_local.
#[export] Hint Resolve kalloc_token_local_facts : saturate_local.

Section Kalloc_ASI.
Variable K: KallocFreeAPD.
Variable kalloc1ID: ident.
Variable kfree1ID: ident.

Definition kalloc1_spec := 
   DECLARE (*_kalloc*)kalloc1ID
   WITH n:Z, gv:globals, original_freelist_pointer:val
   PRE [ ]
       PROP (0 <= n <= Ptrofs.max_unsigned(* - (WA+WORD)*) /\ is_pointer_or_null original_freelist_pointer)
       PARAMS () GLOBALS (gv)
       SEP ( mem_mgr K gv )
   POST [ tptr tvoid ]
       PROP ()
       RETURN (original_freelist_pointer)
       SEP ( mem_mgr K gv;
             if eq_dec original_freelist_pointer nullval then emp
             else (kalloc_token' K sh n original_freelist_pointer * memory_block sh n original_freelist_pointer)).

Definition kfree1_spec :=
 DECLARE (*_kfree*)kfree1ID
   WITH n:Z, p:val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr K gv;
            if eq_dec p nullval then emp
            else (kalloc_token' K sh n p * memory_block sh n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr K gv).

Definition Kalloc_ASI:funspecs := [kalloc1_spec; kfree1_spec].
End Kalloc_ASI.