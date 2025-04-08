Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(*Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.*)
Require Import VC.VSU_kalloc_kfree_definitions.

Lemma body_kfree1 i: semax_body MF_Vprog MF_Gprog f_kfree1 (kfree1_spec KF_APD i).
Proof. start_function.
Admitted.

Lemma body_kalloc1 i: semax_body MF_Vprog MF_Gprog f_kalloc1 (kalloc1_spec KF_APD i).
Proof. start_function. 
Admitted.
