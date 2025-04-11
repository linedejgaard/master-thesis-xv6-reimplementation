Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import VC.tactics.
Require Import VC.ASI_kalloc.
Require Import VC.kalloc.

#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined.

(* ================================================================= *)
(** ** Size-based kalloc tokens *)

Definition kalloc_token_sz (sh: share) (n: Z) (p: val) : mpred :=
  !! ((*field_compatible t_run [] p /\*)
      0 < n <= PGSIZE
      /\ malloc_compatible (n) p 
      /\ malloc_compatible (PGSIZE) p
      /\ writable_share sh
      (*/\  maybe some alignment and physical address checks here *))
  && memory_block sh (n) (p).

Lemma kalloc_token_sz_valid_pointer:
  forall (sh : share) (sz : Z) (p : val),
  kalloc_token_sz sh sz p |-- valid_pointer p.
Proof.
  intros. 
  unfold kalloc_token_sz. entailer.
Qed.

Lemma  kalloc_token_sz_local_facts : 
 forall (sh : share) (n:Z) (p : val) ,
   kalloc_token_sz sh n p |-- !! malloc_compatible n p.
Proof.
  intros. 
  unfold kalloc_token_sz. simpl. entailer.
Qed.

Lemma kalloc_token_sz_split:
forall  (sh: share) (n: Z) (p: val),
  kalloc_token_sz sh n p =
  !! ((*field_compatible t_run [] p /\*)
  0 < n <= PGSIZE
  /\ malloc_compatible (n) p 
  /\ malloc_compatible (PGSIZE) p
  /\ writable_share sh
  (*/\  maybe some alignment and physical address checks here *))
  && memory_block sh (n) (p).
Proof.
  intros. apply pred_ext.
  - unfold kalloc_token_sz. entailer.
  - unfold kalloc_token_sz. entailer!.
Qed.


(* ================================================================= *)
(** ** Defining freelistrep *)

Definition PGSIZE : Z := 4096.
Definition t_run := Tstruct _run noattr.
Definition t_struct_kmem := Tstruct _struct_kmem noattr.

(* NOTE: assume PGSIZE is greater than sizeof t_run *)
Fixpoint freelistrep (sh: share) (il: list val) (p: val) : mpred := (* the list contains the next*)
 match il with
 | next::il' =>
        !! malloc_compatible (PGSIZE) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        (sepcon (data_at sh t_run next p) (* at the location p, there is a t_run structure with the value next *)
        (freelistrep sh il' next) (* "*" ensures no loops... *))
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

(* ================================================================= *)
(** ** Defining APD: use tokens based on size *)

Definition Tok_APD := Build_KallocTokenAPD kalloc_token_sz kalloc_token_sz_valid_pointer
  kalloc_token_sz_local_facts.

Definition mem_mgr_internal (gv: globals) (sh : share) (ls: list val) (xx:Z) (original_freelist_pointer:val): mpred := (* I am unsure how to access all these elements.. *)
    !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).

Definition mem_mgr_external (gv: globals) : mpred :=
  EX (sh : share), EX (ls: list val), EX (xx:Z), EX (original_freelist_pointer:val), (* I am unsure how to access all these elements.. *)
  !! (writable_share sh /\
    is_pointer_or_null original_freelist_pointer /\
          (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
          ((ls <> nil) /\ isptr original_freelist_pointer))
    ) &&
  (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
  (freelistrep sh ls original_freelist_pointer)).

Lemma mem_mgr_internal_entails_mem_mgr_external :
  forall gv sh ls xx original_freelist_pointer,
    mem_mgr_internal gv sh ls xx original_freelist_pointer
    |-- mem_mgr_external gv.
Proof.
  intros gv sh ls xx original_freelist_pointer.
  unfold mem_mgr_internal.
  unfold mem_mgr_external.
  Intros.
  Exists sh ls xx original_freelist_pointer.
  entailer!.
Qed.

Lemma mem_mgr_local_facts :
  forall gv,
    (mem_mgr_external gv) |-- (EX (sh : share), EX (ls : list val), EX (original_freelist_pointer : val),
      !! (writable_share sh /\
          is_pointer_or_null original_freelist_pointer /\
          (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
           ((ls <> nil) /\ isptr original_freelist_pointer)))).
Proof.
  intros. unfold mem_mgr_external. Intros sh ls xx original_freelist_pointer.
  Exists sh ls original_freelist_pointer.
  entailer!.
Qed.


Definition KF_APD := Build_KallocFreeAPD Tok_APD mem_mgr_external mem_mgr_local_facts.

(* ================================================================= *)
(** ** Constructing Vprog and Gprog *)

Definition KF_ASI: funspecs := Kalloc_ASI KF_APD _kalloc _kfree.
Definition KF_imported_specs:funspecs :=  nil.
Definition KF_internal_specs: funspecs := KF_ASI.
Definition KF_globals_external gv : mpred:= ASI_kalloc.mem_mgr KF_APD gv.
(*Definition KF_globals_internal gv sh ls xx original_freelist_pointer: mpred:= ASI_kalloc.mem_mgr KF_APD gv sh ls xx original_freelist_pointer.*)
Definition KFVprog : varspecs. mk_varspecs kalloc.prog. Defined.
Definition KFGprog: funspecs := KF_imported_specs ++ KF_internal_specs.

(* ================================================================= *)
(** ** Lemma to unfold mem_mgr *)

Lemma mem_mgr_internal_split: 
 forall (gv:globals) (sh:share) (ls: list val) (xx:Z) (original_freelist_pointer:val),
  mem_mgr_internal gv sh ls xx original_freelist_pointer
  = 
  !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).
Proof.
  intros. apply pred_ext.
  - unfold mem_mgr_internal. entailer!.
  - unfold mem_mgr_internal. entailer!.
Qed.

Lemma mem_mgr_external_split: 
 forall (gv:globals),
  mem_mgr_external gv 
  = 
  EX (sh : share), EX (ls: list val), EX (xx:Z), EX (original_freelist_pointer:val),
  !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).
Proof.
  intros. apply pred_ext.
  - unfold mem_mgr_external. entailer!.
  Exists sh ls xx original_freelist_pointer. entailer!.
  - unfold mem_mgr_external. entailer!.
  Exists sh ls xx original_freelist_pointer. entailer!.
Qed.


(*************************)

(* ================================================================= *)

(* ################################################################# *)
(** * Constructing the Component and the VSU *)

Definition KF_Externs : funspecs := nil.

Definition MallocFreeVSU: @VSU NullExtension.Espec
         KF_Externs KF_imported_specs ltac:(QPprog prog) KF_ASI KF_globals_external.
  Proof. 
 mkVSU prog KF_internal_specs.
    (*- dmit. solve_SF_internal body_kalloc.
    - solve_SF_internal body_kfree.
    - solve_SF_internal body_exit.
    - apply initialize; auto.*)
Admitted.

Ltac start_function_hint ::= idtac. (* no hint reminder *)


