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

Lemma positive_product : forall i size,
  0 < i -> 0 < size -> 0 < i * size.
Proof.
  intros i size H1 H2.
  (* We are given i > 0 and PGSIZE > 0, so their product is positive *)
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma PGSIZE_gt_0: 0 < PGSIZE.
Proof.
    unfold PGSIZE; rep_lia.
Qed.

Lemma cmp_le_is_either_0_or_1 : forall p q i,
   sem_cmp_pp Cle p q = Some (Vint i) ->
   (i = Int.zero) \/ (i = Int.one).
Proof.
intros.
destruct (eq_dec i Int.zero). left; auto.
destruct (eq_dec i Int.one). right; auto.
unfold sem_cmp_pp in H. inversion H.
unfold bool2val in H1. unfold Z.b2z in H1. unfold option_map in H1.
destruct (Val.cmplu_bool true2 Cle p q).
- destruct b; inversion H1; exfalso.
   + apply n0; auto.
   + apply n; auto.
- inversion H1.
Qed.


Lemma ptrofs_add_simpl :
  forall a ofs,
    0 <= ofs <= Ptrofs.max_unsigned ->
    0 <= Ptrofs.unsigned a + ofs < Ptrofs.modulus ->
    Ptrofs.unsigned (Ptrofs.add a (Ptrofs.repr ofs)) =
    Ptrofs.unsigned a + ofs.
Proof.
  intros.
  unfold Ptrofs.add.
  rewrite Ptrofs.unsigned_repr.
  - rewrite Ptrofs.unsigned_repr; auto.
  - destruct H; assert (Ptrofs.unsigned (Ptrofs.repr ofs) = ofs). { apply Ptrofs.unsigned_repr; try rep_lia. } split.
    + rewrite H2; try rep_lia.
    + rewrite H2; auto; try rep_lia.
Qed.

Ltac ptrofs_add_simpl_PGSIZE := apply ptrofs_add_simpl; split_lia; unfold PGSIZE; rep_lia.


Lemma typed_true_offset_val_leq (b_s_init b_n_init : block) 
      (p_s_tmp p_n_init : ptrofs) (ofs : Z) :
  typed_true tint
    match sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) (Vptr b_n_init p_n_init) with
    | Some v' => v'
    | None => Vundef
    end ->
  Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr ofs)) <= Ptrofs.unsigned p_n_init.
Proof.
   destruct (sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) 
   (Vptr b_n_init p_n_init)) eqn:e; auto_contradict.
   destruct v; auto_contradict.
   assert (i = Int.zero \/ i = Int.one). { apply cmp_le_is_either_0_or_1 with (p:= (offset_val ofs (Vptr b_s_init p_s_tmp))) (q:=(Vptr b_n_init p_n_init) ); auto. }
   destruct H; subst; auto_contradict.
   unfold sem_cmp_pp in e; simpl in e. destruct (eq_block b_s_init b_n_init); auto_contradict.
   intros. subst.
   destruct ((negb (Ptrofs.ltu p_n_init (Ptrofs.add p_s_tmp (Ptrofs.repr ofs))))) eqn:e1; auto_contradict.
   unfold negb in e1. destruct (Ptrofs.ltu p_n_init (Ptrofs.add p_s_tmp (Ptrofs.repr ofs))) eqn:e2; auto_contradict.
   unfold Ptrofs.ltu in e2. destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr ofs)))) eqn: e3; auto_contradict.
   try rep_lia.
Qed.

Lemma typed_false_offset_val_leq (b_s_init b_n_init : block) 
      (p_s_tmp p_n_init : ptrofs) (ofs : Z) :
   Ptrofs.unsigned p_s_tmp + ofs < Ptrofs.modulus -> (* I know the ofs =PGSIZE*)
   0 <= ofs <= Ptrofs.max_unsigned ->
   typed_false tint
      match sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) (Vptr b_n_init p_n_init) with
      | Some v' => v'
      | None => Vundef
      end ->
   Ptrofs.unsigned p_n_init < Ptrofs.unsigned p_s_tmp + ofs.
Proof.
   destruct (sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) 
   (Vptr b_n_init p_n_init)) eqn:e; auto_contradict.
   destruct v; auto_contradict.
   assert (i = Int.zero \/ i = Int.one). { apply cmp_le_is_either_0_or_1 with (p:= (offset_val ofs (Vptr b_s_init p_s_tmp))) (q:=(Vptr b_n_init p_n_init) ); auto. }
   destruct H; subst; auto_contradict.
   subst. unfold sem_cmp_pp in e. simpl in e. destruct (eq_block b_s_init b_n_init); auto_contradict.
   destruct ((negb (Ptrofs.ltu p_n_init (Ptrofs.add p_s_tmp (Ptrofs.repr ofs))))) eqn:e1; auto_contradict.
   unfold negb in e1; unfold Ptrofs.ltu in e1. destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr ofs)))) eqn:e2; auto_contradict.
   intros.
   assert (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr ofs)) = Ptrofs.unsigned p_s_tmp + ofs) by ptrofs_add_simpl_PGSIZE.
   rewrite <- H2. unfold PGSIZE; apply l.
Qed.

Lemma sameblock_true :
forall b_s_init b_n_init p_s_tmp p_n_init,
   sameblock (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) = true ->
   b_s_init = b_n_init.
Proof.
   intros. unfold sameblock in H.
   destruct (peq b_s_init b_n_init); try rep_lia; auto_contradict.
Qed.

Lemma sameblock_false :
forall b_s_init b_n_init p_s_tmp p_n_init,
   sameblock (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) = false ->
   b_s_init <> b_n_init.
Proof.
   intros. unfold sameblock in H.
   destruct (peq b_s_init b_n_init); try rep_lia; auto_contradict.
Qed.


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


(* add offset *)
Ltac unfold_size size ename :=
  destruct (Z.leb 0 size) eqn:ename;
  try rep_lia.

Definition add_offset (p: val) (ofs: Z) : val := 
   match p with
   | Vptr b1 p1 => 
      if (Z.leb 0 ofs) then
         Vptr b1 (Ptrofs.add p1 (Ptrofs.repr ofs)) 
      else
         nullval
   | _ => nullval
   end.

Lemma add_offset_correct:
   forall b p size,
      0 <= size ->
     add_offset (Vptr b p) size = Vptr b (Ptrofs.add p (Ptrofs.repr size)).
Proof.
   intros. unfold add_offset. destruct (0 <=? size) eqn:es; try rep_lia. reflexivity.
Qed.

Lemma add_offset_0:
   forall p,
    isptr p ->
    add_offset p 0 = p.
Proof.
   intros. destruct p; auto_contradict. unfold add_offset. rewrite ptrofs_add_repr_0_r; auto.
Qed.

(* subtract offset *)

Definition sub_offset (p: val) (ofs: Z) : val := 
   match p with
   | Vptr b1 p1 => Vptr b1 (Ptrofs.sub p1 (Ptrofs.repr ofs))
   | _ => nullval
   end.

Lemma sub_offset_correct:
   forall b p size,
     sub_offset (Vptr b p) size = Vptr b (Ptrofs.sub p (Ptrofs.repr size)).
Proof.
   intros. unfold sub_offset. reflexivity.
Qed.

Lemma sub_add_offset_correct:
   forall p size,
   0 < size ->
   isptr p ->
   sub_offset (add_offset p size) size = p.
Proof.
intros; destruct p; auto_contradict.
  unfold add_offset, sub_offset.
  destruct (0 <=? size) eqn:es; try rep_lia.
  rewrite Ptrofs.sub_add_opp.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_neg_zero. 
  rewrite Ptrofs.add_zero; auto.
Qed.

Lemma sub_add_offset_n:
   forall p size n,
   0 < size ->
   (0 < n) ->
   isptr p ->
   sub_offset (add_offset p (n*size)) size = add_offset p ((n-1)*size).
Proof.
intros; destruct p; auto_contradict.
  unfold add_offset, sub_offset.
  unfold_size (n * size)%Z e1.
  unfold_size ((n -1)* size)%Z e2.
  -rewrite Ptrofs.sub_add_opp.
   rewrite Ptrofs.add_assoc.
   rewrite<- ptrofs_mul_repr.
   rewrite<- ptrofs_mul_repr.
   rewrite <- ptrofs_sub_repr.
   assert (Ptrofs.mul (Ptrofs.neg (Ptrofs.repr 1)) (Ptrofs.repr size) = Ptrofs.neg (Ptrofs.repr size)). {
      rewrite <- Ptrofs.neg_mul_distr_l.
      replace (Ptrofs.repr 1) with Ptrofs.one; auto.
      rewrite Ptrofs.mul_commut.
      rewrite Ptrofs.mul_one; auto.
   }
   rewrite Ptrofs.sub_add_opp.
   rewrite Ptrofs.mul_add_distr_l.
   rewrite <- H2. auto.
  -rewrite Z.leb_gt in e2.
  destruct n; try rep_lia.
  assert ((Z.pos p - 1) >= 0)%Z by lia.
  assert ((Z.pos p - 1) * size >= 0)%Z by nia.
  try rep_lia.
Qed.

Lemma add_sub_offset_correct:
   forall p size,
   0 < size ->
   isptr p ->
     add_offset (sub_offset p size) size = p.
Proof.
intros; destruct p; auto_contradict.
unfold add_offset, sub_offset.
rewrite <- Ptrofs.sub_add_l.
rewrite Ptrofs.sub_add_opp.
rewrite Ptrofs.add_assoc.
rewrite Ptrofs.add_neg_zero. 
rewrite Ptrofs.add_zero; auto.
unfold_size size e; auto.
Qed.

Lemma add_offset_eq_offset_val:
  forall pa1 size,
    0 < size ->
    isptr pa1 ->
    add_offset pa1 size = offset_val size pa1.
Proof.
  intros pa1 size H.
  destruct pa1; try contradiction.
  (* pa1 is a Vptr *)
  unfold add_offset, offset_val.
  simpl. unfold_size size e.
  reflexivity.
Qed.

Lemma add_offset_isptr:
   forall p size,
   0 < size ->
   isptr p ->
   isptr (add_offset p size).
Proof.
   intros.
   unfold add_offset; destruct p; auto_contradict.
   auto.
   unfold_size size e; auto.
Qed.

Lemma add_offset_add:
  forall (pa1:val) (i size : Z),
    0 < size->
    isptr pa1 ->
    0 <= i ->
    add_offset (add_offset pa1 (i * size)) size =
    add_offset pa1 ((i + 1) * size).
Proof.
   intros pa1 i size H.
   unfold add_offset. destruct pa1; auto_contradict.
   f_equal.
   unfold_size (i * size)%Z e.
   unfold_size size e1.
   unfold_size ((i + 1) * size)%Z e2.
   rewrite Ptrofs.add_assoc.
   rewrite ptrofs_add_repr.
   assert (i * size + size = ((i + 1) * size)%Z); try rep_lia.
   rewrite H0; auto.
Qed.

(** is pointers *)
Fixpoint isptr_lst (n: nat) (p: val) (size: Z) : Prop :=
  match n with
  | S n' => 
      (isptr p) /\ (isptr_lst n' (add_offset p size) size)
  | O => isptr p (* TODO: is this correct?? *)
  end.

(* list of pointers *)
Fixpoint pointers_acc (n: nat) (p: val) (size: Z) (acc: list val) : list val :=
  match n with
  | O => acc
  | S n' => pointers_acc n' (add_offset p size) size (p :: acc)
  end.

(*Definition pointers (n: nat) (p: val) (size: Z) : list val :=
   pointers_acc n p size nil.*)

Lemma pointers_acc_correct:
   forall n size q acc,
   pointers_acc (S n) q size acc = pointers_acc n (add_offset q size) size (q :: acc).
Proof.
   intros.
   unfold pointers_acc; fold pointers_acc; auto.
Qed.

Lemma add_to_pointers:
  forall n p size,
    isptr p ->
    (0 <= n)%nat ->
    add_offset p (Z.of_nat n * size) :: pointers_acc n p size [] =
    pointers_acc n (add_offset p size) size [p].
Proof.
  intros n. induction n as [|n IH]; intros.
  - (* base case *)
    simpl. rewrite add_offset_0 by auto. reflexivity.
  - (* inductive case *)
   unfold pointers_acc.
    rewrite <- IH.
Admitted.

Definition pointers_with_original_head (n: nat) (p: val) (size: Z) (head:val): list val :=
   match n with
   | O => nil
   | S O => [head]
   | S n' => pointers_acc n' p size [head]
   end.

Definition get_curr_head (n: nat) (p: val) (size: Z) (head:val): val :=
   match n with
   | O => nullval
   | S O => head
   | S n' => add_offset p (Z.of_nat n' * size)
   end.

(*Lemma get_head_correct:
   forall n p size head,
   isptr p ->
   hd nullval (pointers_with_original_head n p size head) = get_curr_head n p size head.
Proof.
intros.
induction n.
- simpl. auto.
- unfold get_curr_head. destruct n eqn:en.
+ simpl. auto.
+ unfold pointers_with_original_head. unfold pointers_acc. unfold add_offset. simpl.
Admitted.*)

Lemma get_head_ls_correct:
   forall n p size head ls,
   (0 < n)%nat ->
   isptr p ->
   hd nullval (pointers_with_original_head n p size head ++ ls) = get_curr_head n p size head.
Proof.
intros.
induction n.
- rep_lia.
- unfold get_curr_head. destruct n eqn:en.
+ simpl. auto.
+ unfold pointers_with_original_head. unfold pointers_acc. unfold add_offset. simpl.
Admitted.

Lemma hd_add_offset_ls:
   forall n p size original_head ls,
   0 < n ->
   isptr p ->
      add_offset p (n * size) = hd nullval
      (pointers_with_original_head (Z.to_nat n + 1) p size
      original_head ++ ls).
Proof.
   intros n.
   induction n; unfold pointers_acc; intros; try rep_lia.
   rewrite get_head_ls_correct; auto; try rep_lia.
   unfold get_curr_head.
   destruct ((Z.to_nat (Z.pos p) + 1)%nat) eqn:e; try rep_lia.
   destruct n; try rep_lia.
   assert ((Z.to_nat (Z.pos p))%nat = (S n)); try rep_lia.
   rewrite <- H1.
   replace (Z.of_nat (Z.to_nat (Z.pos p))) with ( (Z.pos p)); try rep_lia; auto.
Qed.


Lemma add_to_pointers_with_head: (* TODO: I think n should be greater than 0.. *)
   forall n p size head,
   isptr p ->
   add_offset p (Z.of_nat n * size) :: pointers_acc n p size [head] =
   pointers_acc n (add_offset p size) size [p; head].
Proof.
   intros.
   induction n; unfold pointers_acc.
   - rewrite add_offset_0; auto.
   - fold pointers_acc. rewrite <- pointers_acc_correct with (q:=(add_offset p size)); auto.
   rewrite <- pointers_acc_correct with (q:=p); auto.
   unfold pointers_acc; fold pointers_acc. rewrite<- IHn.
Admitted.

Lemma pointers_acc_length:
  forall (n : nat) (p : val) (size : Z) (acc : list val),
    length (pointers_acc n p size acc) = (n + length acc)%nat.
Proof.
  induction n as [| n' IH]; intros.
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. rewrite <- plus_n_Sm. auto.
Qed.

Lemma pointers_with_head_non_empty:
   forall n p size head,
   isptr p ->
   (0 < n)%nat ->
   pointers_with_original_head n p size head <> [].
Proof.
   intros.
   destruct n eqn:en; try rep_lia.
   unfold not.
   unfold pointers_with_original_head. destruct n0.
   - intros; auto_contradict.
   - intros. destruct n0. unfold pointers_acc in H1; auto_contradict.
   assert (length (pointers_acc (S (S n0)) p size [head]) = (O)). {
      rewrite H1. auto.
   } 
   assert (length (pointers_acc ((S (S n0))) p size [head]) = (((S (S n0))) + length [head])%nat). {
      apply pointers_acc_length.
   }
   rewrite H3 in H2. try rep_lia.
Qed.

   
(*Lemma pointers_empty :
   forall p size,
   nil = pointers 0 p size.
Proof.
   intros. unfold pointers; auto.
Qed.*)

Lemma pointers_with_head_empty :
   forall p size head,
   nil = pointers_with_original_head 0 p size head.
Proof.
   intros. unfold pointers_with_original_head; auto.
Qed.


(* available and available range *)

Fixpoint available (sh: share) (n: nat) (p: val) (size: Z) : mpred :=
  match n with
  | S n' => 
      EX v,
      !! malloc_compatible (sizeof t_run) p &&  (* Check memory compatibility *)
      data_at sh t_run v p *            (* Store null value *)
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
  - unfold available. entailer!. split; split; intros; auto; auto_contradict; try rep_lia.
  - unfold available. Intros v. destruct p; entailer!. split; split; intros; try rep_lia; auto; auto_contradict.
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
   EX m : nat, EX v: val,
          !! (n = S m) && !! malloc_compatible (sizeof t_run) x && data_at sh t_run v x * available sh m (add_offset x size) size.
Proof.
   intros; apply pred_ext.
   - destruct n. 
         + unfold available. entailer!.
         + unfold available; fold available. Intros v.
         Exists n. Exists v. entailer!.
   - Intros m v. rewrite H0. unfold available at 2; fold available. Exists v. entailer!.
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
   (EX v,
    !! malloc_compatible (sizeof t_run) p &&
    data_at sh t_run v p * available sh n (add_offset p size) size).
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

Ltac refold_available :=
  unfold available;
  fold available.



(****************** compare pointers range *********************)
Fixpoint ensure_comparable (sh: share) (n: nat) (p q: val) (size: Z) : mpred :=
  match n with
  | S n' =>
      denote_tc_test_order p q &&
      ensure_comparable sh n' (add_offset p size) q size
  | O => !! (p = nullval) && emp
  end.

Definition ensure_comparable_range (sh: share) (p_start p_end: val) (size: Z) :=
   match p_start, p_end with
   | Vptr b_s p_s, Vptr b_e p_e =>
      if sameblock p_start p_end then
         ensure_comparable sh (Z.to_nat ((compute_c p_start p_end size) + 1)) p_start p_end size
      else !! (p_start = nullval) && emp
   | _ , _ => !! (p_start = nullval) && emp
   end.



(* there are more lemmas in verif_simple kfree file v2*)