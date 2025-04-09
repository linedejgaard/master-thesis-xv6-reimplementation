(********************** functional model and lemmas for clients *************)
Require Import VST.floyd.proofauto.
Require Import VC.clients.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined. 
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_pipe := Tstruct _pipe noattr.

(*Local Open Scope logic.*)

Definition pipe_rep sh (pi: val) : mpred :=
   EX data,
  data_at sh t_struct_pipe
    ( (* data = uninitialized? depends on model *)
      (data), (* array data[PIPESIZE] *)
      (Vint (Int.repr 0), (* nread *)
      (Vint (Int.repr 0), (* nwrite *)
      (Vint (Int.repr 1), (* readopen *)
       Vint (Int.repr 1)  (* writeopen *))))
    ) pi.