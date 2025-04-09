(********************** functional model and lemmas for clients *************)
Require Import VST.floyd.proofauto.
Require Import VC.tactics.
Require Import VC.kalloc.

#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined.

Local Open Scope logic.

Definition PGSIZE : Z := 4096.
Definition t_run := Tstruct _run noattr.
Definition t_struct_kmem := Tstruct _struct_kmem noattr.


(************************ freelistrep *********************************)
(* NOTE: assume PGSIZE is greater than sizeof t_run *)
Fixpoint freelistrep (sh: share) (il: list val) (p: val) : mpred := (* the list contains the next*)
 match il with
 | next::il' =>
        !! malloc_compatible (PGSIZE) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        data_at sh t_run next p * (* at the location p, there is a t_run structure with the value next *)
        freelistrep sh il' next (* "*" ensures no loops... *)
 | nil => !! (p = nullval) && emp
 end.

Arguments freelistrep sh il p : simpl never.

Lemma freelistrep_local_prop: forall sh n p, 
   freelistrep sh n p |--  !! (is_pointer_or_null p /\ (n=nil<->p=nullval) /\ ((n <> nil)<->isptr p))%nat.
Proof.
  intros.
  induction n as [| n' IH].
  - unfold freelistrep. entailer!. split; auto.
    + split; auto.
    + split; try lia. intros. simpl in *. auto_contradict. intros; auto_contradict.
  - unfold freelistrep. destruct p; entailer!. split.
    + split; intros; inversion H2.
    + split; intros; auto. unfold not; intros. auto_contradict.
   Qed.
#[export] Hint Resolve freelistrep_local_prop : saturate_local.

Lemma freelistrep_valid_pointer:
  forall sh n p, 
  readable_share sh ->
   freelistrep sh n p |-- valid_pointer p.
Proof.
  intros. destruct n.
  - unfold freelistrep. entailer!.
  - unfold freelistrep. entailer.
Qed. 
#[export] Hint Resolve freelistrep_valid_pointer : valid_pointer.

Ltac refold_freelistrep :=
  unfold freelistrep;
  fold freelistrep.



(************* kallocfun ***************)

Definition t_struct_pipe := Tstruct _pipe noattr.

Local Open Scope logic.

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