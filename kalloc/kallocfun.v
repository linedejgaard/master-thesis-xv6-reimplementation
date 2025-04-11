(********************** functional model and lemmas for clients *************)
Require Import VST.floyd.proofauto.
Require Import VC.tactics.
Require Import VC.kalloc.
Require Import VC.ASI_kalloc.

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




(****************** loops *********************)

Definition compute_c (p_start p_end: val) (size: Z) : Z :=
  match p_start, p_end with
  |  Vptr b1 p1 , Vptr b2 p2 =>
        if (size <=? 0)%Z then 0 (* Avoid division by zero *)
        else if (Ptrofs.ltu p2 p1) then 0 (* we don't want p2 < p1, meaning we have p1 <= p2, when we have a real result *)
        else
          (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size (* take the floor *)
  | _ , _ => 0
  end.
 
Lemma compute_c_equal :
  forall p_start p_end size,
  0 < size ->
  p_start = p_end ->
  compute_c p_start p_end size = 0.
Proof.
  intros. unfold compute_c. destruct p_start; auto.
  destruct p_end; auto.
  destruct (size <=? 0); auto.
  unfold Ptrofs.ltu.
  destruct (zlt (Ptrofs.unsigned i0) (Ptrofs.unsigned i)); auto.
  inversion H0. subst. replace (Ptrofs.unsigned i0 - Ptrofs.unsigned i0) with (0); try rep_lia.
  apply Z.div_0_l; try rep_lia.
Qed.

Lemma compute_c_not_equal :
forall p_start p_end size pt_s pt_e b,
0 < size ->
p_start <> p_end ->
Ptrofs.unsigned pt_s < Ptrofs.unsigned  pt_e ->
Vptr b pt_s = p_start ->
Vptr b pt_e = p_end ->
compute_c p_start p_end size =  (Ptrofs.unsigned pt_e - Ptrofs.unsigned pt_s) / size.
Proof.
  intros. unfold compute_c.
  rewrite <- H2. rewrite <- H3.
  destruct (size <=? 0) eqn:e; try rep_lia.
  unfold Ptrofs.ltu; destruct (zlt (Ptrofs.unsigned pt_e) (Ptrofs.unsigned pt_s)) eqn:e1; try rep_lia.
Qed.

Lemma compute_c_correct1:
forall b (p1 p2: ptrofs) size,
    (*0 < size ->
    Ptrofs.unsigned p1 <= Ptrofs.unsigned p2 -> *)
    0 < size ->
    Ptrofs.unsigned p1 <= Ptrofs.unsigned p2 ->
    Ptrofs.unsigned p1 + (size * (compute_c (Vptr b p1) (Vptr b p2) size)) <= Ptrofs.unsigned p2.
Proof.
    intros.
    unfold compute_c.
    destruct (size <=? 0); try rep_lia.
    unfold Ptrofs.ltu; destruct (zlt (Ptrofs.unsigned p2) (Ptrofs.unsigned p1)) eqn:e1; try rep_lia.
    assert ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) = size * ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size) + (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) by (apply Z.div_mod; rep_lia). 
    destruct ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) eqn:em; auto_contradict.
    - rewrite Z.add_comm. rewrite Z.le_add_le_sub_r. rewrite H1 at 2. rewrite Z.add_0_r.
    assert ((1*((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size))%Z = ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size)) by rep_lia. 
    rewrite <- H2 at 1. apply Z.mul_le_mono_nonneg_l; try rep_lia.
    - rewrite Z.add_comm; rewrite Z.le_add_le_sub_r; rewrite H1 at 2.
        assert ((1*((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size))%Z = ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size)) by rep_lia.
        apply Z.le_trans with (m:= (size * ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size))%Z); try rep_lia.
    - assert (0 <= (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) by (apply Z_mod_nonneg_nonneg; try rep_lia).
        rewrite em in H2; auto_contradict. 
    Qed.

Lemma compute_c_correct2:
    forall b (p1 p2: ptrofs) size,
    0 < size ->
    Ptrofs.unsigned p1 <= Ptrofs.unsigned p2 ->
    (Ptrofs.unsigned p2 - (Ptrofs.unsigned p1 + ((compute_c (Vptr b p1) (Vptr b p2) size)*size)%Z)) <= size.
Proof.
    intros. unfold compute_c.
    destruct (size <=? 0) eqn:e; try rep_lia.
    unfold Ptrofs.ltu; destruct (zlt (Ptrofs.unsigned p2) (Ptrofs.unsigned p1)) eqn:e1; try rep_lia.
    assert ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) = size * ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size) + (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) by (apply Z.div_mod; rep_lia).
    rewrite Z.le_sub_le_add_r.
    rewrite Z.add_assoc. rewrite Z.add_comm. rewrite Z.add_assoc. rewrite <- Z.le_sub_le_add_r.
    rewrite H1 at 1.
    destruct ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) eqn:em; auto_contradict.
    - rewrite Z.mul_comm. apply Zplus_le_compat_l; rep_lia.
    - rewrite Z.mul_comm. apply Zplus_le_compat_l. rewrite <- em.
        assert (0 <= (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size < size). { apply Z.mod_pos_bound; auto. }
        destruct H2. apply Z.lt_le_incl; auto.
    - rewrite Z.mul_comm. apply Zplus_le_compat_l; rep_lia.
Qed.

Fixpoint kalloc_tokens token (K:KallocFreeAPD) (sh: share) (n: nat) (p: val) (size: Z) (t:type): mpred :=
  match n with
  | S n' => 
      token K sh (sizeof t) p  *
      kalloc_tokens token K sh n' (offset_val size p) size t (* Move to the next slot *)
  | O => !! (p = nullval) && emp
  end.

Definition kalloc_tokens_range token K (sh: share) (p_start p_end: val) (size: Z) :=
    match p_start, p_end with
    | Vptr b_s p_s, Vptr b_e p_e =>
      if (sameblock p_start p_end) then
        kalloc_tokens token K sh (Z.to_nat (compute_c p_start p_end size)) p_start size
      else !! (p_start = nullval) && emp
    | _ , _ => !! (p_start = nullval) && emp
    end.

Arguments kalloc_tokens_range token K sh p_start p_end size : simpl never.

Lemma kalloc_tokens_local_prop: forall token K sh n p size t, 
  kalloc_tokens token K sh n p size t |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros token K sh n.
  induction n as [| n' IH].
  - unfold kalloc_tokens. entailer!. split; split; intros; auto; auto_contradict; try rep_lia.
  - unfold kalloc_tokens; fold kalloc_tokens. intros. sep_apply IH. entailer!. destruct p; auto_contradict.
  split; split; intros; try rep_lia; auto; auto_contradict.
  + split; intros; auto_contradict.
  + split; intros; auto; rep_lia.
Qed.
#[export] Hint Resolve kalloc_tokens_local_prop : saturate_local.

Lemma add_add_offset_n:
   forall p size n,
   0 < size ->
   (0 < n) ->
   isptr p ->
   offset_val size (offset_val (n * size) p) = offset_val ((n + 1) * size) p.
Proof.
intros; destruct p; auto_contradict.
  - unfold offset_val.
  simpl. f_equal.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite<- ptrofs_mul_repr.
  rewrite<- ptrofs_mul_repr.
  rewrite <- ptrofs_add_repr.
  (*rewrite <- ptrofs_sub_repr.*)
  (*rewrite Ptrofs.sub_add_opp.*)
  rewrite Ptrofs.mul_add_distr_l.
  replace (Ptrofs.repr 1) with (Ptrofs.one); auto.
  replace (Ptrofs.mul Ptrofs.one (Ptrofs.repr size)) with (Ptrofs.repr size). 
  2: {
  rewrite Ptrofs.mul_commut.
  rewrite Ptrofs.mul_one with (x:=Ptrofs.repr size). auto.
  }
  auto.
Qed.

Lemma sub_add_offset_n:
   forall p size n,
   0 < size ->
   (0 < n) ->
   isptr p ->
   offset_val (-size) (offset_val (n*size) p) = offset_val ((n-1)*size) p.
Proof.
intros; destruct p; auto_contradict.
  - unfold offset_val.
  simpl. f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite <- Ptrofs.neg_repr.
  f_equal.
  rewrite<- ptrofs_mul_repr.
  rewrite<- ptrofs_mul_repr.
  rewrite <- ptrofs_sub_repr.
  rewrite Ptrofs.sub_add_opp.
  rewrite Ptrofs.mul_add_distr_l.
  assert (Ptrofs.mul (Ptrofs.neg (Ptrofs.repr 1)) (Ptrofs.repr size) = Ptrofs.neg (Ptrofs.repr size)). {
    rewrite <- Ptrofs.neg_mul_distr_l.
    replace (Ptrofs.repr 1) with Ptrofs.one; auto.
    rewrite Ptrofs.mul_commut.
    rewrite Ptrofs.mul_one; auto.
  } rewrite H2. auto.
Qed.

Fixpoint pointers (n: nat) (p: val) (size: Z) : list val :=
  match n with
  | O => []
  | S n' => p :: pointers n' (offset_val size p) size
  end.

Definition pointers_rev n p size := rev (pointers n p size).

Lemma fold_pointers_rev :
  forall n size q,
  pointers_rev n q size = rev (pointers n q size).
Proof.
  intros. unfold pointers_rev; auto.
Qed.

Lemma pointers_correct:
  forall n size q,
  pointers_rev (S n) q size = pointers_rev n (offset_val size q) size ++ [q].
Proof.
  intros.
  unfold pointers_rev, pointers. fold pointers. 
  destruct n.
  - simpl. reflexivity.
  - simpl. auto.
Qed.

Lemma pointers_offset_eq : 
  forall n p size, 
    isptr p -> 
    pointers n p size ++ [offset_val (Z.of_nat n * size) p] = 
    pointers (S n) p size.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl. intros p size H. rewrite Z.mul_0_l. unfold offset_val; destruct p; auto_contradict.
    rewrite Ptrofs.add_zero.
    reflexivity.
  - (* Inductive case: n = S n' *)
  unfold pointers. fold pointers. intros.
  assert (offset_val (Z.of_nat (S n') * size) p = offset_val (Z.of_nat (n') * size) (offset_val size p)). {
    rewrite offset_offset_val.
    assert (size + Z.of_nat n' * size = (Z.of_nat (S n') * size)%Z). { try rep_lia. }
    rewrite H0. auto.
  }
  rewrite H0. 
  assert ( (pointers n' (offset_val size p) size) ++
        [offset_val (Z.of_nat n' * size) (offset_val size p)] = 
        pointers (S n') (offset_val size p) size
        ). { apply IHn'. auto. }
  rewrite <- app_comm_cons. rewrite H1.
  unfold pointers. fold pointers. auto.
Qed.

Lemma add_to_pointers:
 forall n p size,
  isptr p ->
   (offset_val (Z.of_nat n * size)%Z p) :: pointers_rev (n) p size =
   pointers_rev n (offset_val size p) size ++ [p].
Proof.
  intros.
  rewrite <- pointers_correct.
  unfold pointers_rev, pointers. fold pointers.
  rewrite <- rev_unit.
  f_equal.
  induction n.
  - simpl; auto. rewrite Z.mul_0_l. unfold offset_val; destruct p; auto_contradict. rewrite Ptrofs.add_zero; auto.
  - unfold pointers; fold pointers. rewrite <- app_comm_cons. f_equal. 
  assert (offset_val (Z.of_nat (S n) * size) p = offset_val (Z.of_nat (n) * size) (offset_val size p)). {
    rewrite offset_offset_val.
    assert (size + Z.of_nat n * size = (Z.of_nat (S n) * size)%Z). { try rep_lia. }
    rewrite H0. auto.
  }
  rewrite H0.
  rewrite pointers_offset_eq; auto.
Qed.

Definition pointers_with_original_head (n: nat) (p: val) (size: Z) (head:val): list val :=
   match n with
   | O => nil
   | S O => [head]
   | S n' => pointers_rev n' p size ++ [head]
   end.
Lemma pointers_with_head_empty :
   forall p size head,
   nil = pointers_with_original_head 0 p size head.
Proof.
   intros. unfold pointers_with_original_head; auto.
Qed.

Lemma add_to_pointers_with_head:
 forall n p size hd,
  isptr p ->
  (0 < n)%nat ->
   (offset_val (Z.of_nat (n-1) * size)%Z p) :: pointers_with_original_head (n) p size hd =
   pointers_with_original_head (n+1) p size hd.
Proof.
  intros.
  induction (n+1)%nat eqn:e; try rep_lia.
  assert (n = n0); try rep_lia. rewrite H1.
  destruct n0; try rep_lia. 
  unfold pointers_with_original_head.
  replace ((S n0) - 1)%nat  with (n0); try rep_lia.
  destruct n0; try rep_lia.
  - simpl. rewrite isptr_offset_val_zero; auto.
  - assert (offset_val (Z.of_nat (S n0) * size) p :: pointers_rev (S n0) p size = pointers_rev (S (S n0)) p size). {
    rewrite add_to_pointers; auto.
  }
  rewrite <- H2.
  auto.
Qed.