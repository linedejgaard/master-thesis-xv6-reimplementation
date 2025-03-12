Require VC.Preface.  (* Check for the right version of VST *)

(* ----------------------------------------------------------------- *)
(** *** Standard boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VC.sum_inputs_ints.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* ----------------------------------------------------------------- *)
(** *** Functional model *)
Definition sum : Z -> Z -> Z := Z.add.

(*Lemma sum_two_times :
    forall a b c d, sum (a+b) (c+d) = sum a b + sum c d.
Proof.
    unfold sum. try lia. 
Qed. *)

(*Lemma sum_comm :
    forall a b, sum a b = sum b a.
Proof.
    unfold sum. try lia. 
Qed. *)

(** ** API spec for the sum.c program *)

Definition sum_spec : ident * funspec :=
DECLARE _sum
 WITH a: Z,  b: Z
 PRE [ tint, tint ]
  PROP  (
         0 <= a + b <= Int.max_signed; (** Fix this... *)
         0 <= a <= Int.max_signed;
         0 <= b <= Int.max_signed )
  PARAMS (Vint (Int.repr a);Vint (Int.repr b))
  SEP   ()
 POST [ tint ]
  PROP () RETURN (Vint (Int.repr (sum a b)))
  SEP ().


Definition main_spec :=
DECLARE _main
    WITH gv : globals
    PRE [] main_pre prog tt gv
    POST [ tint ] main_post prog gv. (*  *)

Definition main_spec' :=
    DECLARE _main
        WITH gv : globals
        PRE [] main_pre prog tt gv
        POST [ tint ]
        PROP()
        RETURN (Vint (Int.repr (sum 2 2)))
        SEP(TT).
        

(** ** Prove that the c-code satisfies the specification *)
Definition Gprog := [sum_spec; main_spec']. (* Packaging the Gprog and Vprog *)
(* OBS: main_spec also works *)

Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
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
semax_func_cons body_sum.
semax_func_cons body_main.
Qed.