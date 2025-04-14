Require Import VST.floyd.proofauto.

Require Import VC.tactics.
Require Import VC.kalloc.

#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined.

(* ================================================================= *)
(** ** Types and defs *)

Definition PGSIZE : Z := 4096.
Definition t_run := Tstruct _run noattr.
Definition t_struct_kmem := Tstruct _struct_kmem noattr.

(* ================================================================= *)
(** ** Size-based kalloc tokens *)

Definition kalloc_token_sz (sh: share) (n: Z) (p: val) : mpred :=
  !! (
      0 < n <= PGSIZE
      /\ malloc_compatible n p 
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

(* NOTE: assume PGSIZE is greater than sizeof t_run *)
Fixpoint freelistrep (sh: share) (il: list val) (p: val) : mpred := (* the list contains the next*)
 match il with
 | next::il' =>
        !! malloc_compatible (sizeof t_run) p &&  (* p is compatible with a memory block of size sizeof theader. *)
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

Definition freelistrep_safe sh il p :=
  !! NoDup il && freelistrep sh il p.

