Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
Require Import VC.Spec_kalloc.

(*#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.*)

Local Open Scope logic.

(*Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.*)
Require Import VC.VSU_kalloc_kfree_definitions.

Lemma body_kfree1 i: semax_body MF_Vprog MF_Gprog f_kfree1 (kfree1_spec_sz KF_APD i).
Proof. start_function. Intros.
forward.
rewrite mem_mgr_split. Intros.
destruct (eq_dec new_head nullval).
- forward_if.
    * rewrite e in H2; auto_contradict.
    * forward. entailer. rewrite mem_mgr_split. entailer.
- forward_if.
    * Intros. forward. intros. rewrite kalloc_token_sz_split. Intros.
    rewrite memory_block_data_at_.
     forward.
    * forward. entailer.
Admitted.


Lemma body_kalloc1 i: semax_body MF_Vprog MF_Gprog f_kalloc1 (kalloc1_spec (KF_APD) i).
Proof. start_function.
rewrite mem_mgr_split. Intros. forward.  unfold abbreviate in POSTCONDITION.
forward_if (
    PROP  ( )
    LOCAL (
        temp _r original_freelist_pointer; 
        gvars gv
        )
    SEP (
        ASI_kalloc.mem_mgr KF_APD gv sh ls xx original_freelist_pointer*
                   (if eq_dec original_freelist_pointer nullval
                   then emp
                   else kalloc_token' KF_APD sh PGSIZE original_freelist_pointer)
    )
)%assert.
+forward. destruct H0 as [[H0011 H0012] | [H0021 H0022]].
    - rewrite H0012 in H1; auto_contradict.
    - destruct ls; auto_contradict.
    refold_freelistrep. Intros.
    forward. forward.
    destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.
    rewrite mem_mgr_split. Exists sh (v::ls) xx original_freelist_pointer. entailer!.
    refold_freelistrep. entailer.
    rewrite kalloc_token'_split. Exists v. entailer. admit.
+ forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.
    rewrite mem_mgr_split. Exists sh ([]:list val) xx nullval. entailer!. destruct H0 as [[H011 H012]| [H021 H022]]; auto_contradict.
    rewrite H011. entailer.
+ destruct (eq_dec original_freelist_pointer nullval) eqn:e1. 
    *forward. Exists nullval. entailer.
    * forward. Exists original_freelist_pointer. entailer!. destruct (eq_dec original_freelist_pointer nullval) eqn:e2; auto_contradict.
    entailer.
Admitted. 