(* ----------------------------------------------------------------- *)
(** *** Standard boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VC.sum.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* ----------------------------------------------------------------- *)
(** *** Functional model *)
Definition sum_2_2 : Z := Z.add 2 2.

(*Lemma sum_Z_4:
    sum_2_2 = 4.
Proof.
    unfold sum_2_2. try lia. 
Qed.*)

(** ** API spec for the sum.c program *)

Definition sum_2_2_spec : ident * funspec :=
DECLARE _sum_2_2
 WITH u : unit
 PRE [ ]
  PROP  ()
  PARAMS ()
  SEP   ()
 POST [ tint ]
  PROP () RETURN (Vint (Int.repr sum_2_2))
  SEP ().

Definition main_spec :=
DECLARE _main
    WITH gv : globals
    PRE [] main_pre prog tt gv  (* The main_pre function typically ensures that the global variables are initialized correctly and that any necessary resources are available before executing the main function. *)
    POST [ tint ] main_post prog gv. (* The main_post function specifies the conditions that must hold after the main function has executed. This typically includes the expected return value of the main function and the final state of the global variables. *)

Definition main_spec' :=
    DECLARE _main
        WITH gv : globals
        PRE [] main_pre prog tt gv
        POST [ tint ]
        PROP()
        RETURN (Vint (Int.repr (sum_2_2)))
        SEP(TT).
        

(** ** Prove that the c-code satisfies the specification *)
Definition Gprog := [sum_2_2_spec; main_spec']. (* Packaging the Gprog and Vprog *)
(* OBS: main_spec also works *)

Lemma body_sum_2_2: semax_body Vprog Gprog f_sum_2_2 sum_2_2_spec.
Proof.
    start_function.
    repeat forward.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec'.
Proof.
    start_function.
    forward_call. forward. 
Qed.

#[export] Existing Instance NullExtension.Espec. (* boilerplate, when you don't have input/output *)

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sum_2_2.
semax_func_cons body_main.
Qed.