Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.clients.
Require Import VC.helper.
Require Import VC.Spec_kalloc.

(*#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.*)

Local Open Scope logic.

(*Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.*)
Require Import VC.VSU_kalloc_kfree_definitions.

Lemma body_kfree1: semax_body MF_Vprog MF_Gprog f_kfree1 (kfree1_spec KF_APD t_run).
Proof. start_function. Intros.
forward.
rewrite mem_mgr_split. Intros.
destruct (eq_dec new_head nullval).
- forward_if.
    * rewrite e in H2; auto_contradict.
    * forward. entailer. rewrite mem_mgr_split. entailer.
- forward_if.
    * Intros. forward. unfold my_kalloc_token. Intros. rewrite kalloc_token_sz_split. Intros. 
    rewrite memory_block_data_at_; auto. forward. forward. 
    (*forward. intros. rewrite kalloc_token_sz_split. Intros.
    rewrite memory_block_data_at_.
     forward.*) entailer. rewrite mem_mgr_split. refold_freelistrep. entailer!.
     right; split; auto. unfold not; auto_contradict.
    * forward. entailer.
Qed.


Lemma body_kalloc1: semax_body MF_Vprog MF_Gprog f_kalloc1 (kalloc1_spec (KF_APD) t_run).
Proof. start_function.
rewrite mem_mgr_split. Intros. forward.  (*unfold abbreviate in POSTCONDITION.*)
forward_if (
    PROP  ( )
    LOCAL (
        temp _r original_freelist_pointer; 
        gvars gv
        )
    SEP (
        if (eq_dec original_freelist_pointer nullval) then
        (ASI_kalloc.mem_mgr KF_APD gv sh ls xx original_freelist_pointer * emp)
      else 
        (
          EX next ls',
          (!! (next :: ls' = ls) &&
              my_kalloc_token KF_APD sh (t_run) original_freelist_pointer *
              ASI_kalloc.mem_mgr KF_APD gv sh ls' xx next
          )
        )
        (*ASI_kalloc.mem_mgr KF_APD gv sh ls xx original_freelist_pointer*
                   (if eq_dec original_freelist_pointer nullval
                   then emp
                   else my_kalloc_token KF_APD sh t_run original_freelist_pointer)*)
    )
)%assert.
- destruct H3 as [[H0011 H0012] | [H0021 H0022]].
    + rewrite H0012 in H4; auto_contradict.
    + destruct ls; auto_contradict.
    refold_freelistrep. Intros.
    forward. (*unfold abbreviate in POSTCONDITION.*) forward.
    entailer.
    (*destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.*)
    rewrite mem_mgr_split. Intros. 
    refold_freelistrep. if_tac.
    * rewrite H11 in H0022; auto_contradict.
    * entailer. Exists v ls. entailer. unfold my_kalloc_token.
    rewrite kalloc_token_sz_split. rewrite mem_mgr_split. entailer!.
    -- split. unfold malloc_compatible. destruct original_freelist_pointer; auto_contradict. 
        unfold malloc_compatible in H3. destruct H3. split; auto.
        try rep_lia.
        destruct ls.
        ++ left; split; auto. rewrite <- H9; auto.
        ++ right. split.
            **  unfold not. intros; auto_contradict.
            ** rewrite <- H10. unfold not; intros; auto_contradict.
    -- apply data_at_memory_block.
-forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.
rewrite mem_mgr_split. entailer.
- if_tac; forward.
Qed.

