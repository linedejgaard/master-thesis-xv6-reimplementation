Require Import VST.floyd.proofauto.

Require Import VC.tactics.
Require Import VC.kalloc.

#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined.

(* ================================================================= *)
(** ** Types and defs *)

Definition PGSIZE : Z := 4096.
Definition t_run := Tstruct _run noattr.
Definition t_struct_kmem := Tstruct _struct_kmem noattr.

Definition t_run_size := sizeof t_run.

(* ================================================================= *)
(** ** Size-based kalloc tokens *)

Definition forall_small_PGSIZE p : Prop :=
  (forall n : Z, (0 < n <= PGSIZE /\ ((isptr p /\ 0 < n <= PGSIZE /\ malloc_compatible (n) p)))).
  (*ALL n : Z, !! (0 < n <= PGSIZE /\ ((isptr p /\ 0 < n <= PGSIZE /\ malloc_compatible (n) p) \/ (p = nullval))).*)

Definition kalloc_token_sz (sh: share) (n: Z) (p: val) : mpred :=
  !! (
      0 < n <= PGSIZE 
      /\ forall_small_PGSIZE p
      /\ writable_share sh
      /\ field_compatible t_run [] p (* make sure t_run fits*)
      /\ malloc_compatible (sizeof t_run) p 
      /\ 0 < (sizeof t_run) <= PGSIZE 
      /\ match p with
         | Vptr _ ofs => Ptrofs.unsigned ofs + PGSIZE < Ptrofs.modulus
         | _ => True
         end
      (*/\  maybe some alignment and physical address checks here *))
  && ((*sepcon (forall_small_PGSIZE p) *)
  (sepcon (memory_block sh (t_run_size) (p)) (memory_block sh (PGSIZE - t_run_size)
  (offset_val t_run_size p))) ).

Lemma kalloc_token_sz_valid_pointer:
  forall (sh : share) (sz : Z) (p : val),
  kalloc_token_sz sh sz p |-- valid_pointer p.
Proof.
  intros. 
  unfold kalloc_token_sz. unfold t_run_size. entailer.
Qed.

Lemma  kalloc_token_sz_local_facts : 
 forall (sh : share) (n:Z) (p : val) ,
   kalloc_token_sz sh n p |-- !! malloc_compatible n p.
Proof.
  intros. 
  unfold kalloc_token_sz. Intros. entailer. unfold forall_small_PGSIZE in H0.
  specialize (H0 n). entailer!.
  destruct H0 as [HH0 [HH1 [HH2 HH3]]].
  auto. 
Qed.

Lemma kalloc_token_sz_split:
forall  (sh: share) (n: Z) (p: val),
  kalloc_token_sz sh n p =
  !! (
      0 < n <= PGSIZE 
      /\ forall_small_PGSIZE p
      /\ writable_share sh
      /\ field_compatible t_run [] p (* make sure t_run fits*)
      /\ malloc_compatible (sizeof t_run) p 
      /\ 0 < (sizeof t_run) <= PGSIZE 
      /\ match p with
         | Vptr _ ofs => Ptrofs.unsigned ofs + PGSIZE < Ptrofs.modulus
         | _ => True
         end
      (*/\  maybe some alignment and physical address checks here *))
  && ((*sepcon (forall_small_PGSIZE p) *)
  (sepcon (memory_block sh (t_run_size) (p)) (memory_block sh (PGSIZE - t_run_size)
  (offset_val t_run_size p))) ).
Proof.
  intros. apply pred_ext.
  - unfold kalloc_token_sz. entailer.
  - unfold kalloc_token_sz. entailer!.
Qed.

Lemma token_merge :
forall (sh: share) (p:val) b i,
isptr p ->
p = Vptr b i ->
PGSIZE + Ptrofs.unsigned i < Ptrofs.modulus ->
(sepcon (memory_block sh t_run_size p)
  (memory_block sh (PGSIZE - t_run_size) (offset_val t_run_size p)) 
  = memory_block sh PGSIZE p
  ).
Proof.
destruct p; auto_contradict.
assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH. { rewrite Ptrofs.repr_unsigned. auto. }
unfold offset_val. rewrite Ptrofs.add_unsigned.
rewrite Ptrofs.unsigned_repr.
intros.
rewrite HH at 1.
rewrite <- memory_block_split.
assert (t_run_size + (PGSIZE - t_run_size) = PGSIZE) as Hpgsz; try rep_lia.
rewrite Hpgsz. rewrite HH at 2. auto.
- unfold t_run_size. simpl; try rep_lia.
- unfold t_run_size. simpl; try rep_lia.
- unfold t_run_size. simpl; try rep_lia. split; try rep_lia.
inversion H0. unfold PGSIZE in H1; auto.
- unfold t_run_size. simpl; try rep_lia.
Qed.


(* ================================================================= *)
(** ** Defining freelistrep *)


(* NOTE: assume PGSIZE is greater than sizeof t_run *)
Fixpoint freelistrep (sh: share) (il: list val) (p: val) : mpred := (* the list contains the next*)
 match il with
 | next::il' =>
        (!!(malloc_compatible (sizeof t_run) p 
          /\ match p with
          | Vptr _ ofs => Ptrofs.unsigned ofs + PGSIZE < Ptrofs.modulus
          | _ => True
          end
          /\
          forall_small_PGSIZE p
          ) &&  (* p is compatible with a memory block of size sizeof theader. *)
          (
          (sepcon (sepcon (data_at sh t_run next p) 
                    (memory_block sh (PGSIZE - t_run_size) (offset_val t_run_size p))) (* at the location p, there is a t_run structure with the value next *)
          (freelistrep sh il' next) (* "*" ensures no loops... *))))
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
  - unfold freelistrep. fold freelistrep. destruct p; entailer!. split.
    + split; intros; inversion H5.
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

