Require VC.Preface.  (* Check for the right version of VST *)

(* ----------------------------------------------------------------- *)
(** *** Standard boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VC.sum.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* ----------------------------------------------------------------- *)
(** *** Functional model *)
Definition sum_2_2 : Z := Z.add 2 2.

Lemma sum_Z_4:
    sum_2_2 = 4.
Proof.
    unfold sum_2_2. try lia. 
Qed.

(** ** API spec for the sum.c program *)

Definition sum_2_2_spec : ident * funspec :=
DECLARE _sum_2_2
 WITH u : unit
 PRE [ ]
  PROP  ()
  PARAMS ()
  SEP   ()
 POST [ tuint ]
  PROP () RETURN (Vint (Int.repr 4))
  SEP ().

Definition main_spec :=
DECLARE _main
    WITH gv : globals
    PRE [] main_pre prog tt gv
    POST [ tint ] main_post prog gv.

(** ** Prove that the c-code satisfies the specification *)
(*Definition Gprog := [sum_2_2_spec; main_spec].*)
Definition Gprog : funspecs :=   ltac:(with_library prog [sum_2_2_spec; main_spec]).

Lemma body_sum_2_2: semax_body Vprog Gprog f_sum_2_2 sum_2_2_spec.
Proof.
Admitted.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
Admitted.

#[export] Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sum_2_2.
semax_func_cons body_main.
Qed.