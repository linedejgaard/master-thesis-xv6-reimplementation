(* Do not edit this file, it was generated automatically *)
Require Import VST.floyd.proofauto.
Require Import VC.nest2_modified_remove_a.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_struct_b := Tstruct _b noattr.

Definition get_spec' :=
 DECLARE _get
  WITH v : reptype' t_struct_b, gv: globals
  PRE  []
        PROP ()
        PARAMS() GLOBALS (gv)
        SEP(data_at Ews t_struct_b (repinj _ v) (gv _p))
  POST [ tint ]
         PROP()
         RETURN (Vint (v))
         SEP (data_at Ews t_struct_b (repinj _ v) (gv _p)).

Definition get_spec :=
 DECLARE _get
  WITH v : (int)%type, gv: globals
  PRE  []
        PROP ()
        PARAMS() GLOBALS (gv)
        SEP(data_at Ews t_struct_b (Vint v) (gv _p))
  POST [ tint ]
         PROP()
         RETURN (Vint (v))
         SEP (data_at Ews t_struct_b (Vint v) (gv _p)).

Definition update22 (i: int) (v: reptype' t_struct_b) : reptype' t_struct_b :=
   (i).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_b, gv: globals
  PRE  [ tint ]
         PROP  ()
         PARAMS (Vint i) GLOBALS (gv)
         SEP   (data_at Ews t_struct_b (Vint v) (gv _p))
  POST [ tvoid ]
         PROP() RETURN()
        SEP(data_at Ews t_struct_b (Vint (update22 i v)) (gv _p)).

Definition main_spec' :=
       DECLARE _main
       WITH gv : globals
       PRE [] main_pre prog tt gv
       POST [ tint ]
       PROP()
       RETURN (Vint (Int.repr (42)))
       SEP(TT).

Definition main_spec :=
       DECLARE _main
       WITH gv : globals
       PRE [] main_pre prog tt gv
       POST [ tint ] main_post prog gv.
              
Definition Gprog : funspecs :=   ltac:(with_library prog [get_spec; set_spec; main_spec]).

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
start_function.
simpl in v.
unfold_repinj.
Time forward. (* 5.989 sec  -> 2.6 -> 1.5 *)
Time forward. (* 11.1118 sec -> 7.5 *)
Time Qed.

Lemma body_get':  semax_body Vprog Gprog f_get get_spec'.
Proof.
start_function.
simpl in v.
unfold_repinj.
Time forward. (* 5.989 sec  -> 2.6*)
Time forward. (* 11.1118 sec -> 7.5 *)
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
simpl in v.
(*destruct v as [a [b c]]; simpl in *. *)
unfold_repinj.
Time forward. (* 1.23 sec *)
entailer!!.
Time Qed.  (*  28 sec -> 3.45 sec *)

Definition fortytwo := (Int.repr 42).
Definition v : (int)%type :=  (Int.repr 0).

Lemma body_main: semax_body Vprog Gprog f_main main_spec. (* Lost here *)
Proof.
    start_function.
    forward_call (fortytwo, v, gv).
    2 : {
       forward_call (update22 (Int.repr 42) v, gv); try entailer!.
       forward.
    }
    unfold t_struct_b.
    sep_apply data_at_data_at_ .
    
    entailer!.


    Check data_at__local_facts.
    sep_apply data_at__local_facts. 
Admitted.


#[export] Existing Instance NullExtension.Espec. (* boilerplate, when you don't have input/output *)

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
prove_semax_prog.
Proof.
semax_func_cons body_get.
semax_func_cons body_set.
semax_func_cons body_main.
Qed.




