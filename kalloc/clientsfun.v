(********************** functional model and lemmas for clients *************)
Require Import VST.floyd.proofauto.
Require Import VC.tactics.
Require Import VC.kalloc.
Require Import VC.ASI_kalloc.

#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined.

Local Open Scope logic.


(************* clients fun ***************)

Definition t_struct_pipe := Tstruct _pipe noattr.

Definition pipe_rep sh (pi: val) : mpred :=
  EX data,
  data_at sh t_struct_pipe
    (
      (data), (* array data[PIPESIZE] *)
      (Vint (Int.repr 0), (* nread *)
      (Vint (Int.repr 0), (* nwrite *)
      (Vint (Int.repr 1), (* readopen *)
       Vint (Int.repr 1)  (* writeopen *))))
    ) pi.