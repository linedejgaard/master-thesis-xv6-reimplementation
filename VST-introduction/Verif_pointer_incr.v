Require VC.Preface.  (* Check for the right version of VST *)

(* ----------------------------------------------------------------- *)
(** *** Standard boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VC.pointer_incr.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* ----------------------------------------------------------------- *)
(** *** Functional model *)
Definition increment (num : Z) : Z := Z.add num 1.


(** ** API spec for the sum.c program *)

Definition increment_spec :=
  DECLARE _increment
  WITH p: val, v: Z
  PRE [ tptr tint ]
    PROP (Int.min_signed <= v < Int.max_signed (* Ensure no overflow *)
          (* Fix: is these assumptions ok? *)
     ) 
    PARAMS (p)
    GLOBALS ()
    SEP (data_at Tsh tint (Vint (Int.repr v)) p) (* `p` points to `v` *)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (v + 1))) (* Return the incremented value *)
    SEP (data_at Tsh tint (Vint (Int.repr (v + 1))) p). (* `p` now holds `v + 1` *)

Definition main_spec :=
    DECLARE _main
    WITH gv : globals
    PRE [] main_pre prog tt gv
    POST [ tint ] main_post prog gv.

(* THIS DOESN'T WORK??? WHAT DOES main_post prog v mean??
Definition main_spec' :=
    DECLARE _main
    WITH gv : globals
    PRE [] main_pre prog tt gv
    POST [ tint ]
        PROP ()
        RETURN (Vint (Int.repr 11)) (* Final return value *)
        SEP ().
        *)

(** ** Prove that the c-code satisfies the specification *)
Definition Gprog := [increment_spec; main_spec]. (* Packaging the Gprog and Vprog *)
(* OBS: main_spec also works *)

Lemma body_increment: semax_body Vprog Gprog f_increment increment_spec.
Proof.
    start_function.
    repeat forward.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
    start_function.
    forward.
    forward_call (v_value, 10).
    forward.
    entailer!.
Qed.

#[export] Existing Instance NullExtension.Espec. (* boilerplate, when you don't have input/output *)

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_increment.
semax_func_cons body_main.
Qed.