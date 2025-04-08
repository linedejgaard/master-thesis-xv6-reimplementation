Require Import VST.floyd.proofauto.
Require Import VC.client1.
Require Import VC.helper.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

