Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VC.kalloc.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Require Import VC.hints.  (* Import special hints for this tutorial. *)
