Require Import VST.floyd.proofauto.
Require Import VC.tactics.
Require Import VC.ASI_kalloc.
Require Import VC.kalloc.
Require Import VC.Spec_kalloc.
Require Import VC.kallocfun.
Require Import VC.Kalloc_APD.

Local Open Scope logic.

Lemma body_kfree: semax_body KAFVprog KAFGprog f_kfree (kfree_spec KAF_APD t_run).
Proof. start_function. Intros.
forward.
rewrite mem_mgr_split. Intros.
destruct (eq_dec new_head nullval).
- forward_if.
    * rewrite e in H2; auto_contradict.
    * forward. entailer. rewrite mem_mgr_split. entailer.
- forward_if.
    * Intros. forward. unfold type_kalloc_token. Intros. rewrite kalloc_token_sz_split. Intros. 
     rewrite memory_block_data_at_; auto. forward. forward. 
     entailer. rewrite mem_mgr_split. refold_freelistrep. entailer!.
     right; split; auto. unfold not; auto_contradict.
    * forward. entailer.
Qed.

Lemma body_kalloc: semax_body KAFVprog KAFGprog f_kalloc (kalloc_spec (KAF_APD) t_run).
Proof. start_function.
rewrite mem_mgr_split. Intros. forward.
forward_if (
    PROP  ( )
    LOCAL (
        temp _r original_freelist_pointer; 
        gvars gv
        )
    SEP (
        if (eq_dec original_freelist_pointer nullval) then
        (ASI_kalloc.mem_mgr KAF_APD gv sh ls xx original_freelist_pointer * emp)
      else 
        (
          EX next ls',
          (!! (next :: ls' = ls) &&
              type_kalloc_token KAF_APD sh (t_run) original_freelist_pointer *
              ASI_kalloc.mem_mgr KAF_APD gv sh ls' xx next
          )
        )
    )
)%assert.
- destruct H3 as [[H0011 H0012] | [H0021 H0022]].
    + rewrite H0012 in H4; auto_contradict.
    + destruct ls; auto_contradict.
    refold_freelistrep. Intros.
    forward. forward.
    entailer.
    rewrite mem_mgr_split. Intros. 
    refold_freelistrep. if_tac.
    * rewrite H11 in H0022; auto_contradict.
    * entailer. Exists v ls. entailer. unfold type_kalloc_token.
    rewrite kalloc_token_sz_split. rewrite mem_mgr_split. entailer!.
    -- destruct ls.
        ++ left; split; auto. rewrite <- H9; auto.
        ++ right. split.
            **  unfold not. intros; auto_contradict.
            ** rewrite <- H10. unfold not; intros; auto_contradict.
    -- apply data_at_memory_block.
-forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.
rewrite mem_mgr_split. entailer.
- if_tac; forward.
Qed.

