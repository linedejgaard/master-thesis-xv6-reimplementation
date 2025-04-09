(** abstract spec interface *)
Require Import VST.floyd.proofauto.
Require Import VC.helper.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.VSU_kalloc_kfree_definitions.

Global Open Scope funspec_scope.

Definition kfree1_spec (K:KallocFreeAPD) {cs: compspecs} (t: type) := 
  DECLARE _kfree1
      WITH new_head:val, gv:globals, sh:share, ls: list val, xx:Z, original_freelist_pointer:val
      PRE [ tptr tvoid]
        PROP(
              is_pointer_or_null new_head
              ) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
          ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer;
          if eq_dec new_head nullval then emp
          else (my_kalloc_token sh (t) new_head (* data_at_ Ews t new_head*))
        )
      POST [ tvoid ]
        PROP()
        RETURN () 
        SEP (
          if eq_dec new_head nullval then 
          ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer
          else 
          ASI_kalloc.mem_mgr K gv sh (original_freelist_pointer::ls) xx new_head
            ).

Definition kalloc1_spec (K:KallocFreeAPD) {cs: compspecs} (t: type) :=
DECLARE _kalloc1
WITH n:Z, gv:globals, sh:share, ls: list val, xx:Z, original_freelist_pointer:val
PRE [ ]
    PROP(0 <= n <= PGSIZE;
            complete_legal_cosu_type t = true;
            natural_aligned natural_alignment t = true) 
    PARAMS () GLOBALS(gv)
    SEP ( ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer )  
POST [ tptr tvoid ]
    PROP()
    RETURN (original_freelist_pointer) 
    SEP (
      if (eq_dec original_freelist_pointer nullval) then
      ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer * emp
      else 
        (
          EX next ls',
          (!! (next :: ls' = ls) &&
              my_kalloc_token sh t original_freelist_pointer *
              ASI_kalloc.mem_mgr K gv sh ls' xx next
        )
        )
    ).

  Lemma kalloc1_spec_sub:
    forall  (K:KallocFreeAPD) {cs: compspecs} (t: type), 
      funspec_sub (snd (kalloc1_spec_sz K _kalloc1)) (snd (kalloc1_spec K t)).
   Proof.
     do_funspec_sub. 
      entailer.
      Exists w emp. entailer.
      repeat destruct w.
      repeat destruct p.
      entailer.
      entailer!. intros. destruct (EqDec_val (eval_id ret_temp x) nullval).
      entailer!.
      Intros next ls'. Exists next ls'.
      entailer!.
      admit.
Admitted.

Lemma kfree1_spec_sub:
forall  (K:KallocFreeAPD) {cs: compspecs} (t: type), (* TODO: fix: this is not general, but it uses KF_APD *)
  funspec_sub (snd (kfree1_spec_sz KF_APD _kfree1)) (snd (kfree1_spec KF_APD t)).
Proof.
  do_funspec_sub. 
  destruct w.
  repeat (destruct p).
  Exists (sizeof t, v0, g0, s, l, z, v) emp.
  entailer!.
  destruct (EqDec_val v0 nullval) eqn:Heq; entailer.
  unfold my_kalloc_token. entailer.
Qed.