Require Import VST.floyd.proofauto.
Require Import VC.client1.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.
Definition t_run := Tstruct _run noattr.
Definition t_struct_kmem := Tstruct _struct_kmem noattr.
Definition PGSIZE : Z := 4096.

(************************ Helper functions and tactics  *************************)

Ltac auto_contradict := try discriminate; try contradiction.
Ltac split_lia := split; try rep_lia.
Ltac simplify_signed_PGSIZE := rewrite Int.signed_repr; unfold PGSIZE; try rep_lia.

Lemma S_pred : forall n, ((S n) - 1)%nat = n.
Proof. lia. Qed.


(****************** range available *********************)

(* compute c

    p1 + c + ? = p2 
    ? <= size
    ? = p2 - (p1 + c)
    p2 - (p1 + c) <= size
*)

Definition compute_c (p_start p_end: val) (size: Z) : Z :=
   match p_start, p_end with
   |  Vptr b1 p1 , Vptr b2 p2 =>
         if (size <=? 0)%Z then 0 (* Avoid division by zero *)
         else if (Ptrofs.ltu p2 p1) then 0 (* we don't want p2 < p1, meaning we have p1 <= p2, when we have a real result *)
         else
          (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size (* take the floor *)
   | _ , _ => 0
   end.

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

(* add offset *)

Definition add_offset (p: val) (ofs: Z) : val := 
   match p with
   | Vptr b1 p1 => Vptr b1 (Ptrofs.add p1 (Ptrofs.repr ofs))
   | _ => nullval
   end.

Lemma add_offset_correct:
   forall b p size,
     add_offset (Vptr b p) size = Vptr b (Ptrofs.add p (Ptrofs.repr size)).
Proof.
   intros. unfold add_offset. reflexivity.
Qed.

(* available and available range *)

Fixpoint available (sh: share) (n: nat) (p: val) (size: Z) : mpred :=
  match n with
  | S n' => 
      !! malloc_compatible (sizeof t_run) p &&  (* Check memory compatibility *)
      data_at sh t_run nullval p *            (* Store null value *)
      available sh n' (add_offset p size) size (* Move to the next slot *)
  | O => !! (p = nullval) && emp
  end.

Definition available_range (sh: share) (p_start p_end: val) (size: Z) :=
   match p_start, p_end with
   | Vptr b_s p_s, Vptr b_e p_e =>
      if (sameblock p_start p_end) then
         available sh (Z.to_nat (compute_c p_start p_end size)) p_start size
      else !! (p_start = nullval) && emp
   | _ , _ => !! (p_start = nullval) && emp
   end.

Arguments available_range sh p_start p_end size : simpl never.


Lemma available_local_prop: forall sh n p size, 
   available sh n p size |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros.
  induction n as [| n' IH].
  - unfold available. entailer!. split; auto.
    + split; auto.
    + split; try lia. intros. simpl in *. inversion H.
  - unfold available. destruct p; entailer!. split; split; intros; try rep_lia; auto; auto_contradict.
   Qed.
#[export] Hint Resolve available_local_prop : saturate_local.


Lemma available_valid_pointer:
  forall sh n p size, 
  readable_share sh ->
   available sh n p size |-- valid_pointer p.
Proof.
  intros. destruct n.
  - unfold available. entailer!.
  - unfold available. entailer.
Qed. 
#[export] Hint Resolve available_valid_pointer : valid_pointer.

Lemma available_null: forall sh n x size,
       x = nullval ->
       available sh n x size = !! (n = O) && emp.
Proof.
   intros.
   destruct n; unfold available; fold available.
   autorewrite with norm. auto.
   apply pred_ext.
   entailer. 
   destruct n; entailer!; try discriminate H0. 
Qed.

Lemma available_nonnull: forall n sh x size,
   x <> nullval ->
   available sh n x size =
   EX m : nat, 
          !! (n = S m) && !! malloc_compatible (sizeof t_run) x && data_at sh t_run nullval x * available sh m (add_offset x size) size.
Proof.
   intros; apply pred_ext.
   - destruct n. 
         + unfold available. entailer!.
         + unfold available; fold available.
         Exists n. entailer!.
   - Intros m. rewrite H0. unfold available at 2; fold available. entailer!.
Qed.


(** lemmas ***)
Lemma available_0:
  forall sh p size, available sh 0 p size = !! (p = nullval) && emp.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma available_S:
  forall sh n p size,
    available sh (S n) p size =
    !! malloc_compatible (sizeof t_run) p &&
    data_at sh t_run nullval p * available sh n (add_offset p size) size.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma available_range_correct:
  forall sh p_start p_end size,
    available_range sh p_start p_end size |-- available sh (Z.to_nat (compute_c p_start p_end size)) p_start size.
Proof.
  intros.
  unfold available_range.
  destruct p_start, p_end; try apply derives_refl.
  destruct (sameblock (Vptr b i) (Vptr b0 i0)); entailer; auto_contradict.
Qed.