Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.ASI_kalloc.
Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.


Local Open Scope logic.

Lemma body_kfree': semax_body KAFVprog KAFGprog f_kfree (kfree_spec' KAF_APD _kfree).
Proof. start_function.
forward.
destruct (eq_dec new_head nullval).
- forward_if.
    * rewrite e in H0; auto_contradict.
    * forward. entailer. 
- forward_if.
    * rewrite mem_mgr_split. Intros. forward. rewrite kalloc_token_sz_split. Intros. 
    unfold t_run_size. rewrite memory_block_data_at_; auto. 
    rewrite data_at__eq. forward. forward. 
    entailer. rewrite mem_mgr_split. refold_freelistrep. entailer!.
    right; split; auto. unfold not; auto_contradict.
    unfold t_run_size. entailer!.
    * forward. entailer.
Qed.

Lemma body_kalloc': semax_body KAFVprog KAFGprog f_kalloc (kalloc_spec' (KAF_APD) _kalloc).
Proof. start_function.
rewrite mem_mgr_split. Intros. forward.
forward_if (
    PROP  ( )
    LOCAL (
        temp _r orig_head; 
        gvars gv
        )
    SEP (
        if (eq_dec orig_head nullval) then
        (ASI_kalloc.mem_mgr KAF_APD gv sh ls xx orig_head * emp)
      else 
        (
          EX next ls',
          (!! (next :: ls' = ls) &&
              kalloc_token' KAF_APD sh n orig_head *
              ASI_kalloc.mem_mgr KAF_APD gv sh ls' xx next
          )
        )
    )
)%assert.
- destruct H1 as [[H0011 H0012] | [H0021 H0022]].
    + rewrite H0012 in H2; auto_contradict.
    + destruct ls; auto_contradict.
        refold_freelistrep. Intros.
        forward. forward.
        if_tac.
        * entailer.
        * Exists v ls. entailer. 
            rewrite mem_mgr_split. entailer!.
            -- destruct ls.
                ++ left; split; auto. rewrite <- H12; auto.
                ++ right. split; unfold not; intros; auto_contradict.
                rewrite <- H13. auto_contradict.
            -- rewrite kalloc_token_sz_split. entailer!. apply data_at_memory_block.
- forward. if_tac_auto_contradict. entailer. rewrite mem_mgr_split. entailer.
- if_tac; forward.
Qed.



