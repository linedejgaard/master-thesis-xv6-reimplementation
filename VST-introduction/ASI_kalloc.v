Require Import VST.floyd.proofauto.
(*Require Export malloc_lemmas.*) (*Exports the model (constants like WA , plus lemmas)*)

(*Require Import malloc. needed for function and type names but not for compspecs 
Update: Some UPenn grad students proposed to abstract over function identifiers -
doing so in our setup makes ASIs source-program-independent!*)

Global Open Scope funspec_scope.

Record KallocTokenAPD := {
  malloc_token': share -> Z -> val -> mpred;
  malloc_token'_valid_pointer: forall sh sz p, 
      malloc_token' sh sz p |-- valid_pointer p;
  malloc_token'_local_facts:  forall sh sz p, 
      malloc_token' sh sz p |-- !! malloc_compatible sz p;
}.

Record KallocFreeAPD := {
  MF_Tok :> KallocTokenAPD;
  mem_mgr: globals -> mpred;
}.

Definition malloc_token {cs:compspecs} M (sh: share) (t: type) (p: val): mpred := 
   !! field_compatible t [] p && 
   malloc_token' M sh (sizeof t) p.

Lemma malloc_token_valid_pointer: forall {cs: compspecs} M sh t p, 
      malloc_token M sh t p |-- valid_pointer p.
Proof. intros. unfold malloc_token.
 apply andp_left2. apply malloc_token'_valid_pointer.
Qed.

#[export] Hint Resolve malloc_token'_valid_pointer : valid_pointer.
#[export] Hint Resolve malloc_token_valid_pointer : valid_pointer.

Lemma malloc_token_local_facts:  forall {cs: compspecs} M sh t p,
      malloc_token M sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold malloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply malloc_token'_local_facts.
Qed.

#[export] Hint Resolve malloc_token'_local_facts : saturate_local.
#[export] Hint Resolve malloc_token_local_facts : saturate_local.

Section Kalloc_ASI.
Variable M: KallocFreeAPD.
Variable kalloc1ID: ident.
Variable kfree1ID: ident.

Definition kalloc1_spec := 
   DECLARE (*_malloc*)kalloc1ID
   WITH n:Z, gv:globals
   PRE [ size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned(* - (WA+WORD)*))
       PARAMS ((Vptrofs (Ptrofs.repr n))) GLOBALS (gv)
       SEP ( mem_mgr M gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr M gv;
             if eq_dec p nullval then emp
             else (malloc_token' M Ews n p * memory_block Ews n p)).

Definition kfree1_spec :=
 DECLARE (*_kfree*)kfree1ID
   WITH n:Z, p:val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr M gv;
            if eq_dec p nullval then emp
            else (malloc_token' M Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr M gv).

Definition Kalloc_ASI:funspecs := [kalloc1_spec; kfree1_spec].
End Kalloc_ASI.