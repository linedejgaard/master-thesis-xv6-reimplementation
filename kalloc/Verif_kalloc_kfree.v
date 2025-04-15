Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.ASI_kalloc.
Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.


Local Open Scope logic.

(*Lemma body_kfree: semax_body KAFVprog KAFGprog f_kfree (kfree_spec KAF_APD t_run).
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
Qed.*)


Lemma body_kfree': semax_body KAFVprog KAFGprog f_kfree (kfree_spec' KAF_APD _kfree).
Proof. start_function.
forward.
rewrite mem_mgr_split. Intros.
destruct (eq_dec new_head nullval).
- forward_if.
    * rewrite e in H2; auto_contradict.
    * forward. entailer. rewrite mem_mgr_split. entailer.
- forward_if.
    * forward. rewrite kalloc_token_sz_split. Intros. 
    assert (memory_block sh ((sizeof t_run) + (PGSIZE-sizeof t_run)) new_head = memory_block sh PGSIZE new_head).
    {
        simpl. unfold PGSIZE. auto.
    }
    rewrite <- H9.
    destruct new_head; auto_contradict.
    assert (memory_block sh ((sizeof t_run) + (PGSIZE - sizeof t_run)) (Vptr b i) = memory_block sh ((sizeof t_run) + (PGSIZE - sizeof t_run)) (Vptr b (Ptrofs.repr (Ptrofs.unsigned i)))). {
        simpl. rewrite Ptrofs.repr_unsigned. auto.
    }
    rewrite H10.
    rewrite memory_block_split; try rep_lia.
    assert (Vptr b (Ptrofs.repr (Ptrofs.unsigned i)) = Vptr b (i)). { rewrite Ptrofs.repr_unsigned. auto. }
    rewrite memory_block_data_at_.
    Intros.
    rewrite data_at__eq. rewrite H11. forward. forward. 
    entailer. rewrite mem_mgr_split. refold_freelistrep. entailer!.
    right; split; auto. unfold not; auto_contradict. 
    unfold t_run_size. unfold offset_val. rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr.
    entailer!. simpl. try rep_lia. rewrite H11. auto.
    * forward. entailer.
Qed.


Lemma body_kalloc: semax_body KAFVprog KAFGprog f_kalloc (kalloc_spec' (KAF_APD) _kalloc).
Proof. start_function.
rewrite mem_mgr_split. Intros. forward. 
if_tac.
-
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
              kalloc_token' KAF_APD sh n original_freelist_pointer *
              ASI_kalloc.mem_mgr KAF_APD gv sh ls' xx next
          )
        )
    )
)%assert.
+ rewrite H2 in H3. auto_contradict.
+ forward. if_tac; auto_contradict. entailer!.
    rewrite mem_mgr_split. entailer!.
+ if_tac_auto_contradict. forward.
-
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
              kalloc_token' KAF_APD sh n original_freelist_pointer *
              ASI_kalloc.mem_mgr KAF_APD gv sh ls' xx next
          )
        )
    )
)%assert.

+destruct H1 as [[H0011 H0012] | [H0021 H0022]].
    * rewrite H0012 in H3; auto_contradict.
    * destruct ls; auto_contradict.
    refold_freelistrep. Intros.
    forward. forward.
    entailer.
    rewrite mem_mgr_split. Intros. 
    refold_freelistrep. if_tac.
    -- rewrite H14 in H0022; auto_contradict.
    -- entailer. Exists v ls. entailer. unfold type_kalloc_token.
    rewrite kalloc_token_sz_split. rewrite mem_mgr_split. entailer!.
    ++ destruct ls.
     left; split; auto. rewrite <- H10; auto.
     right; split; auto. unfold not; intros. auto_contradict.
     rewrite <- H11. unfold not; intros. auto_contradict.
    ++ 
 
    sep_apply data_at_memory_block. unfold offset_val. destruct original_freelist_pointer; auto_contradict. 
    assert (Ptrofs.add i (Ptrofs.repr t_run_size) = Ptrofs.repr (Ptrofs.unsigned i + t_run_size)). {
    rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; unfold t_run_size; simpl; try rep_lia. auto.
    }
    rewrite H15.
    assert (i = Ptrofs.repr (Ptrofs.unsigned i)). { rewrite Ptrofs.repr_unsigned. auto. }
    replace (i) with (Ptrofs.repr (Ptrofs.unsigned i)) at 1.
    entailer!.
    unfold malloc_compatible. 
    rewrite <- memory_block_split.
    **
    rewrite <- H16 at 1. 
    assert (t_run_size + (PGSIZE - t_run_size) = PGSIZE). { simpl. unfold PGSIZE; try rep_lia. }
    rewrite H19. entailer!.
    ** 
    unfold t_run_size; simpl; try rep_lia.
    **
    unfold PGSIZE, t_run_size; simpl; try rep_lia.
    ** simpl. split; try rep_lia. unfold PGSIZE in H4; try rep_lia.
    + forward. entailer.
    + forward. if_tac_auto_contradict. Intros next ls'.
    Exists next ls'. 
    entailer!.
Qed.



(*Lemma body_kalloc: semax_body KAFVprog KAFGprog f_kalloc (kalloc_spec (KAF_APD) t_run).
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
Qed.*)

