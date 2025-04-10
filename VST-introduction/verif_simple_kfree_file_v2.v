Require Import VST.floyd.proofauto.
Require Import VC.simple_kfree_file.

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

Lemma ptrofs_unsigned_sub_self :
  forall p : ptrofs,
    Ptrofs.unsigned p + - Ptrofs.unsigned p = 0.
Proof. intros p; lia. Qed.

Ltac ptrofs_add_simpl_PGSIZE := apply ptrofs_add_simpl; split_lia; unfold PGSIZE; rep_lia.

Lemma PGSIZE_bounds :
   0 <= PGSIZE <= Ptrofs.max_unsigned.
Proof. unfold PGSIZE; rep_lia. Qed.

Lemma c_tmp_bounds_max:
forall (p_s_init p_s_tmp p_n_init:ptrofs) (c_tmp:Z),
   Ptrofs.unsigned p_s_tmp = Ptrofs.unsigned p_s_init + c_tmp * PGSIZE ->
   0 <= c_tmp ->
   Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init -> 
   Ptrofs.unsigned p_n_init + PGSIZE <= Int.max_signed  -> 
  c_tmp + 1 <= Int.max_signed.
Proof.
      intros.
      apply Z.le_trans with (m := Ptrofs.unsigned p_s_init + c_tmp * PGSIZE + PGSIZE); try rep_lia.
      assert (Ptrofs.unsigned p_s_init + c_tmp * PGSIZE + PGSIZE = Ptrofs.unsigned p_s_init + (c_tmp + 1) * PGSIZE) by rep_lia.
      destruct c_tmp; auto_contradict; unfold PGSIZE; auto; try rep_lia.
Qed.

Lemma c_tmp_bounds:
forall (p_s_init p_s_tmp p_n_init:ptrofs) (c_tmp:Z),
   Ptrofs.unsigned p_s_tmp = Ptrofs.unsigned p_s_init + c_tmp * PGSIZE ->
   0 <= c_tmp ->
   Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init -> 
   Ptrofs.unsigned p_n_init + PGSIZE <= Int.max_signed  -> 
  Int.min_signed <= c_tmp + 1 <= Int.max_signed.
Proof.
      split_lia.
      apply c_tmp_bounds_max with (p_s_init:=p_s_init) (p_s_tmp:=p_s_tmp) (p_n_init:=p_n_init); try rep_lia.
Qed.

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

Lemma typed_true_same_block (b_s_init b_n_init : block) 
      (p_s_tmp p_n_init : ptrofs) (ofs : Z) :
  typed_true tint
    match sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) (Vptr b_n_init p_n_init) with
    | Some v' => v'
    | None => Vundef
    end ->
   b_s_init = b_n_init.
Proof.
   destruct (sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) 
   (Vptr b_n_init p_n_init)) eqn:e; auto_contradict.
   unfold sem_cmp_pp in e. simpl in e.
   destruct (eq_block b_s_init b_n_init); auto_contradict.
   intros; auto.
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

(* solves something like "0 <= a + - a + b" *)
Ltac le_sub_self_add_and_solve :=
  rewrite ptrofs_unsigned_sub_self;
  apply Z.add_nonneg_nonneg;
  unfold PGSIZE;
  rep_lia.

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


(************** pointer comparison **************'*)


Definition pointer_comparison (p q : val) (cmp : comparison) : val :=
   force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp cmp p q))).
Definition pointer_cmp_bool (p q : val) (cmp : comparison) : bool :=
   eq_dec (pointer_comparison p q cmp) (Vint (Int.repr 1)).
Definition pointer_le_bool (p q : val) : bool :=
   pointer_cmp_bool p q Cle.

(************************ freelist rep  *************************)
Fixpoint freelistrep (sh: share) (n: nat) (p: val) : mpred :=
 match n with
 | S n' => EX next: val, 
        !! malloc_compatible (PGSIZE) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        data_at sh t_run next p * (* at the location p, there is a t_run structure with the value next *)
        freelistrep sh n' next (* "*" ensures no loops... *)
 | O => !! (p = nullval) && emp
 end.


Arguments freelistrep sh n p : simpl never.

Lemma freelistrep_local_prop: forall sh n p, 
   freelistrep sh n p |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros.
  induction n as [| n' IH].
  - unfold freelistrep. entailer!. split; auto.
    + split; auto.
    + split; try lia. intros. simpl in *. inversion H.
  - unfold freelistrep. destruct p; Intro y; entailer!. split.
    + split; intros; inversion H2.
    + split; intros; auto. try lia. 
   Qed.
#[export] Hint Resolve freelistrep_local_prop : saturate_local.


Lemma freelistrep_valid_pointer:
  forall sh n p, 
  readable_share sh ->
   freelistrep sh n p |-- valid_pointer p.
Proof.
  intros. destruct n.
  - unfold freelistrep. entailer!.
  - unfold freelistrep. Intro y; entailer.
Qed. 
#[export] Hint Resolve freelistrep_valid_pointer : valid_pointer.


Lemma freelistrep_null: forall sh n x,
       x = nullval ->
       freelistrep sh n x = !! (n = O) && emp.
Proof.
   intros.
   destruct n; unfold freelistrep; fold freelistrep.
   autorewrite with norm. auto.
   apply pred_ext.
   Intros y. entailer. 
   destruct n; entailer!; try discriminate H0. 
Qed.


Lemma freelistrep_nonnull: forall n sh x,
   x <> nullval ->
   freelistrep sh n x =
   EX m : nat, EX next:val,
          !! (n = S m) && !! malloc_compatible (PGSIZE) x && data_at sh t_run next x * freelistrep sh m next.
Proof.
   intros; apply pred_ext.
   - destruct n. 
         + unfold freelistrep. entailer!.
         + unfold freelistrep; fold freelistrep. Intros y.
         Exists n y. entailer!.
   - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. Exists y. entailer!.
Qed.



(****************** range available *********************)

Definition compute_c (p_start p_end: val) (size: Z) : Z :=
   match p_start, p_end with
   |  Vptr b1 p1 , Vptr b2 p2 =>
         if (size <=? 0)%Z then 0 (* Avoid division by zero *)
         else if (Ptrofs.ltu p2 p1) then 0 (* we don't want p2 < p1, meaning we have p1 <= p2, when we have a real result *)
         else
          (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size (* take the floor *)
   | _ , _ => 0
   end.
(*Compute (compute_c (Vptr (Block.repr 0) (Ptrofs.repr 1000)) (Vptr 0 (Ptrofs.repr 5000)) 4096).*)

Definition add_offset (p: val) (ofs: Z) : val := 
   match p with
   | Vptr b1 p1 => Vptr b1 (Ptrofs.add p1 (Ptrofs.repr ofs))
   | _ => nullval
   end.

(*Definition sub_pointers (p_1 p_2: val) : val := 
   match p_1, p_2 with
   | Vptr b1 p1 , Vptr b2 p2 => if (sameblock p_1 p_2) then (Vptr b1 (Ptrofs.sub p1 p2)) else nullval
   | _, _ => nullval
   end.*)

Fixpoint available (sh: share) (n: nat) (p: val) (size: Z) : mpred :=
  match n with
  | S n' => 
      !! malloc_compatible (PGSIZE) p &&  (* Check memory compatibility *)
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
          !! (n = S m) && !! malloc_compatible (PGSIZE) x && data_at sh t_run nullval x * available sh m (add_offset x size) size.
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
    !! malloc_compatible (PGSIZE) p &&
    data_at sh t_run nullval p * available sh n (add_offset p size) size.
Proof.
  intros. simpl. reflexivity.
Qed.


Lemma add_offset_correct:
  forall b p size,
    add_offset (Vptr b p) size = Vptr b (Ptrofs.add p (Ptrofs.repr size)).
Proof.
  intros. unfold add_offset. reflexivity.
Qed.

(*Lemma compute_c_correct1:
  forall b (p1 p2: ptrofs) size,
   (*0 < size ->
    Ptrofs.unsigned p1 <= Ptrofs.unsigned p2 -> *)
    0 < size ->
    Ptrofs.unsigned p1 <= Ptrofs.unsigned p2 ->
    Ptrofs.unsigned p1 + (compute_c (Vptr b p1) (Vptr b p2) size) <= Ptrofs.unsigned p2.
Proof.
   intros.
   unfold compute_c.
   destruct (size <=? 0); try rep_lia.
   unfold Ptrofs.ltu; destruct (zlt (Ptrofs.unsigned p2) (Ptrofs.unsigned p1)) eqn:e1; try rep_lia.
   assert ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) = size * ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size) + (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) by (apply Z.div_mod; rep_lia). 
   destruct ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) eqn:em; auto_contradict.
   - rewrite Z.add_comm. rewrite Z.le_add_le_sub_r. rewrite H1 at 2. rewrite Z.add_0_r.
     assert ((1*((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size))%Z = ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size)) by rep_lia. 
     rewrite <- H2 at 1. apply Z.mul_le_mono_nonneg_r; try rep_lia.
   - rewrite Z.add_comm; rewrite Z.le_add_le_sub_r; rewrite H1 at 2.
      assert ((1*((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size))%Z = ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size)) by rep_lia.
      apply Z.le_trans with (m:= (size * ((Ptrofs.unsigned p2 - Ptrofs.unsigned p1) / size))%Z); try rep_lia.
      rewrite <- H2 at 1. apply Z.mul_le_mono_nonneg_r; try rep_lia. apply Z_div_nonneg_nonneg; try rep_lia.
   - assert (0 <= (Ptrofs.unsigned p2 - Ptrofs.unsigned p1) mod size) by (apply Z_mod_nonneg_nonneg; try rep_lia).
      rewrite em in H2; auto_contradict. 
   Qed.*)

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

(* p1 + c + ? = p2 
   ? <= size
   ? = p2 - (p1 + c)
   p2 - (p1 + c) <= size
*)

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

Lemma available_range_correct:
  forall sh p_start p_end size,
    available_range sh p_start p_end size |-- available sh (Z.to_nat (compute_c p_start p_end size)) p_start size.
Proof.
  intros.
  unfold available_range.
  destruct p_start, p_end; try apply derives_refl.
  destruct (sameblock (Vptr b i) (Vptr b0 i0)); entailer; auto_contradict.
Qed.

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

(* lemmas *)
Lemma ensure_comparable_O:
  forall sh p q size,
    ensure_comparable sh 0 p q size = (!! (p = nullval) && emp).
Proof.
  intros. reflexivity.
Qed.
Lemma ensure_comparable_S:
  forall sh n p q size,
    ensure_comparable sh (S n) p q size =
    (denote_tc_test_order p q &&
     ensure_comparable sh n (add_offset p size) q size).
Proof.
  intros. reflexivity.
Qed.

Lemma ensure_comparable_range_cross_block:
  forall sh p_start p_end size,
    sameblock p_start p_end = false ->
    ensure_comparable_range sh p_start p_end size = (!! (p_start = nullval) && emp).
Proof.
  intros.
  unfold ensure_comparable_range.
  destruct p_start; auto; destruct p_end; auto. rewrite H; auto.
Qed.

Lemma ensure_comparable_range_sound:
  forall sh p_start p_end size,
    sameblock p_start p_end = true ->
    ensure_comparable_range sh p_start p_end size =
    ensure_comparable sh (Z.to_nat ((compute_c p_start p_end size) + 1)) p_start p_end size.
Proof.
  intros.
  unfold ensure_comparable_range.
  assert (Vundef <> Vlong Int64.zero) by (unfold not; intros; auto_contradict).
  destruct p_start; try (rewrite FF_andp); 
  destruct p_end; try (rewrite FF_andp); auto_contradict.
  destruct (sameblock (Vptr b i) (Vptr b0 i0)); try rep_lia; auto.
Qed.

Lemma contradict_ec :
  forall pq pp size,
    0 < size ->
    Ptrofs.unsigned pq >= Ptrofs.unsigned pp ->
    Z.to_nat ((Ptrofs.unsigned pq - Ptrofs.unsigned pp) / size + 1) = 0%nat ->
    False.
Proof.
  intros pq pp size Hsize Hge Hec.
  assert (diff_ge_0 : Ptrofs.unsigned pq - Ptrofs.unsigned pp >= 0) by lia.
  assert (div_ge_0 : 0 <= (Ptrofs.unsigned pq - Ptrofs.unsigned pp) / size) by (apply Z_div_nonneg_nonneg; try rep_lia).
  assert (plus_ge_1 : 1 <= (Ptrofs.unsigned pq - Ptrofs.unsigned pp) / size + 1 ); try rep_lia.
Qed.

Lemma ensure_comparable_range_not_step:
  forall sh (bp bq: block) (pp pq pp_tmp: ptrofs) size,
    (ensure_comparable_range sh (Vptr bp pp) (Vptr bq pq) size) |-- denote_tc_test_order (Vptr bp pp) (Vptr bq pq).
Proof.
   intros.
   unfold ensure_comparable_range.
   destruct (sameblock (Vptr bp pp) (Vptr bq pq)) eqn:eb.
   - apply sameblock_true in eb. subst.
      destruct (Z.to_nat (compute_c (Vptr bq pp) (Vptr bq pq) size + 1)) eqn:ec;
      unfold ensure_comparable.
      + entailer. auto_contradict.
      + apply andp_left1. entailer.
   - entailer. auto_contradict.
Qed.

Lemma ensure_comparable_range_step:
  forall sh (bp bq: block) (pp pq: ptrofs) size,
    0 < size ->
    (ensure_comparable_range sh (Vptr bp pp) (Vptr bq pq) size) |-- denote_tc_test_order (add_offset (Vptr bp pp) size) (Vptr bq pq).
Proof.
   intros.
   unfold ensure_comparable_range.
   destruct (sameblock (Vptr bp pp) (Vptr bq pq)) eqn:eb.
   - apply sameblock_true in eb. subst.
      destruct (Z.to_nat (compute_c (Vptr bq pp) (Vptr bq pq) size + 1)) eqn:ec;
      unfold ensure_comparable.
      + entailer. auto_contradict.
      + fold ensure_comparable. apply andp_left2. destruct n eqn:en.
         * unfold ensure_comparable. entailer!. unfold add_offset, nullval in H0; simpl in H0. inversion H0.
         * unfold ensure_comparable; fold ensure_comparable. apply andp_left1. entailer.
   - unfold denote_tc_test_order. unfold test_order_ptrs. apply sameblock_false in eb.
      destruct (add_offset (Vptr bp pp) size); entailer; auto_contradict.
Qed.



Lemma ensure_comparable_range_arbitrary:
  forall sh (bp bq: block) (pp pq pp_tmp: ptrofs) (c size:Z),
    0 < size ->
    0 <= c ->
    Ptrofs.unsigned pp_tmp = Ptrofs.unsigned pp + c * size ->
    Ptrofs.unsigned pp_tmp <= Ptrofs.unsigned pq ->
    (ensure_comparable_range sh (Vptr bp pp) (Vptr bq pq) size) |-- denote_tc_test_order (add_offset (Vptr bp pp_tmp) size) (Vptr bq pq).
Proof.
   intros.
   induction c; auto_contradict. 
   - rewrite Z.mul_0_l in H1. rewrite Z.add_0_r in H1.
   assert (pp_tmp = pp). { admit. } subst.
      apply ensure_comparable_range_step; auto.
   - unfold ensure_comparable_range. destruct (sameblock (Vptr bp pp) (Vptr bq pq)) eqn:eb.
   2: {
      unfold nullval. simpl. 
      assert (Vptr bp pp <> Vlong Int64.zero). { unfold not. intros. inversion H3. }
      assert ((Vptr bp pp = Vlong Int64.zero) <-> False). { split; intros; auto_contradict. }
      rewrite H4. entailer.
   }
   apply sameblock_true in eb. rewrite eb in *.
   destruct (Z.to_nat (compute_c (Vptr bq pp) (Vptr bq pq) size + 1)) eqn:ec.
   + admit. (*contradiction*) 
   + (*rewrite H1. simpl. apply andp_left2.
      induction n; intros.
      * simpl. entailer!. unfold nullval in H3. inversion H3.
      * unfold compute_c in ec. destruct (size <=? 0) eqn:es; auto_contradict.
   
   unfold ensure_comparable; fold ensure_comparable. unfold Ptrofs.ltu in ec; destruct (zlt (Ptrofs.unsigned pq) (Ptrofs.unsigned pp)) eqn:elt; auto_contradict.
   assert (Z.to_nat ((Ptrofs.unsigned pq - Ptrofs.unsigned pp) / size + 1) = S (Z.to_nat ((Ptrofs.unsigned pq - Ptrofs.unsigned pp) / size))); try rep_lia.
   assert (Z.to_nat(((Ptrofs.unsigned pq - Ptrofs.unsigned pp) / size)) = S n); try rep_lia.*)
   admit.
Admitted.

(*Lemma ensure_comparable_monotone:
  forall sh n1 n2 p q size,
    (n1 <= n2)%nat ->
    ensure_comparable sh n1 p q size |-- ensure_comparable sh n2 p q size.
Proof.
  intros sh n1 n2 p q size Hle.
  generalize dependent p.
  induction Hle; intros.
  - apply derives_refl.
  - rewrite ensure_comparable_S.
    apply andp_right.
    + induction n1. unfold ensure_comparable; simpl. entailer!; try rep_lia. unfold ensure_comparable. admit.
    + apply 
Admitted.*)
(* TODO: not proved... end*)





(************************ specs *********************************)


(*Definition kfree1_freelist_spec := 
   DECLARE _kfree1
      WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat
      PRE [ tptr tvoid]
         PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) 
         PARAMS (new_head) GLOBALS(gv)
         SEP (
            freelistrep sh n original_freelist_pointer *
            (!! malloc_compatible (PGSIZE) new_head &&
            data_at sh (t_run) nullval new_head *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) )
         )
      POST [ tvoid ]
         PROP()
         RETURN () 
         SEP (
            freelistrep sh (S n) new_head *
            data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
            ).*)


Definition kfree1_freelist_spec := 
   DECLARE _kfree1
      WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, size:Z, number_structs:nat
      PRE [ tptr tvoid]
         PROP(writable_share sh; is_pointer_or_null original_freelist_pointer; (Nat.le (S O) (number_structs))) 
         PARAMS (new_head) GLOBALS(gv)
         SEP (
            freelistrep sh n original_freelist_pointer *
            available sh number_structs new_head PGSIZE *
            (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) )
         )
      POST [ tvoid ]
         PROP()
         RETURN () 
         SEP (
            freelistrep sh (S n) new_head *
            available sh (Nat.sub number_structs (S O)) (add_offset new_head PGSIZE) PGSIZE *
            data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
            ).

(************** pointer comparison and freelist **************'*)

Definition freerange_no_loop_no_add_spec :=
   DECLARE _freerange_no_loop_no_add
      WITH sh : share, new_head : val, pa_end : val, 
            original_freelist_pointer : val, xx : Z, gv : globals, n:nat
      PRE [ tptr tvoid, tptr tvoid ]
         PROP (
            writable_share sh;
            is_pointer_or_null original_freelist_pointer
         ) 
         PARAMS (new_head; pa_end) GLOBALS (gv)
         SEP (
            denote_tc_test_order new_head pa_end &&
            (freelistrep sh n original_freelist_pointer *
            (!! malloc_compatible (PGSIZE) new_head &&
            data_at sh (t_run) nullval new_head *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) ))
         )
      POST [ tvoid ]
         PROP ()
         RETURN ()
         SEP (
               if pointer_le_bool new_head pa_end then
               freelistrep sh (S n) new_head *
               data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
            else
               freelistrep sh n original_freelist_pointer *
               (!! malloc_compatible (PGSIZE) new_head &&
               data_at sh (t_run) nullval new_head *
               data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) )
         ).

(************** pointer comparison add + call **************'*)


Definition freerange_no_loop_no_add_1_spec :=
   DECLARE _freerange_no_loop_no_add_1
      WITH sh : share, pa_end : val, b:block, p:ptrofs,
            original_freelist_pointer : val, xx : Z, gv : globals, n:nat
      PRE [ tptr tvoid, tptr tvoid ]
         PROP (
            writable_share sh;
            is_pointer_or_null original_freelist_pointer
         ) 
         PARAMS (Vptr b p; pa_end) GLOBALS (gv)
         SEP (
            denote_tc_test_order ((Vptr b (Ptrofs.add p (Ptrofs.repr (PGSIZE))))) pa_end &&
            (freelistrep sh n original_freelist_pointer *
            (!! malloc_compatible (PGSIZE) (Vptr b p) &&
            data_at sh (t_run) nullval (Vptr b p) *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) ))
         )
      POST [ tvoid ]
         PROP ()
         RETURN ()
         SEP (
            if pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr (PGSIZE)))) pa_end then
               (freelistrep sh (S n) (Vptr b p) *
               data_at sh t_struct_kmem (Vint (Int.repr xx), (Vptr b p)) (gv _kmem))
            else
               (freelistrep sh n original_freelist_pointer *
               (!! malloc_compatible (PGSIZE) (Vptr b p) &&
               data_at sh (t_run) nullval (Vptr b p) *
               data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)))
         ).

(************** while loop ***************)
Definition while_1_5_spec : ident * funspec := (* this is not including admits.. *)
    DECLARE _while_1_5
    WITH b_n_init:block, p_n_init:ptrofs, b_s_init:block, p_s_init:ptrofs
    PRE [  tptr tvoid, tptr tvoid ]
        PROP (
                0 <= Ptrofs.unsigned p_s_init <= Ptrofs.unsigned p_n_init /\
                Z.add (Ptrofs.unsigned p_n_init) PGSIZE <= Int.max_signed /\ 
                Z.add (Ptrofs.unsigned p_s_init) PGSIZE <= Int.max_signed 
            ) (* the highest number is s + PGSIZE when it fails. The highest s + PGSIZE when it succeeds is n, so the highest after this is n + PGSIZE*)
        PARAMS (Vptr b_s_init p_s_init; Vptr b_n_init p_n_init)
        SEP (
         denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_init (Ptrofs.repr PGSIZE))) (Vptr b_n_init p_n_init) &&
         (!! (forall p_s_tmp,
            Ptrofs.unsigned p_s_init <= Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init ->
            (denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE))) (Vptr b_n_init p_n_init)) 
               |-- (denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr (PGSIZE + PGSIZE)))) (Vptr b_n_init p_n_init))
         ))
        )
    POST [ tint ]
    EX c:Z, EX p_s_final:ptrofs,
        PROP (
            Ptrofs.unsigned p_s_final = Z.add (Ptrofs.unsigned p_s_init) (Z.mul c PGSIZE) /\ 
            0 <= c /\ 
            (Ptrofs.unsigned p_s_final) <= (Ptrofs.unsigned p_n_init) /\ 
            (Ptrofs.unsigned p_n_init) < Z.add (Ptrofs.unsigned p_s_final) PGSIZE
            )
        RETURN (Vint (Int.repr (c)))
        SEP (denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_final (Ptrofs.repr PGSIZE)))
        (Vptr b_n_init p_n_init)).

(************** freerange kfree simple ***************)
Definition freerange_while_loop_spec : ident * funspec := (* this is not including admits.. *)
    DECLARE _freerange_while_loop
    WITH b_n_init:block, p_n_init:ptrofs, b_s_init:block, p_s_init:ptrofs, 
            sh : share, original_freelist_pointer : val, xx : Z, gv : globals, n:nat
    PRE [  tptr tvoid, tptr tvoid ]
        PROP (
                0 <= Ptrofs.unsigned p_s_init <= Ptrofs.unsigned p_n_init /\
                Z.add (Ptrofs.unsigned p_n_init) PGSIZE <= Int.max_signed /\ 
                Z.add (Ptrofs.unsigned p_s_init) PGSIZE <= Int.max_signed /\

                writable_share sh /\
                is_pointer_or_null original_freelist_pointer 

            ) (* the highest number is s + PGSIZE when it fails. The highest s + PGSIZE when it succeeds is n, so the highest after this is n + PGSIZE*)
        PARAMS (Vptr b_s_init p_s_init; Vptr b_n_init p_n_init) GLOBALS (gv)
        SEP (
         ensure_comparable_range sh (Vptr b_s_init p_s_init) (Vptr b_n_init p_n_init) PGSIZE 
         (*denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_init (Ptrofs.repr PGSIZE))) (Vptr b_n_init p_n_init)*) &&
         (((freelistrep sh n original_freelist_pointer)
            * available_range sh (Vptr b_s_init p_s_init) (Vptr b_n_init p_n_init) PGSIZE
            * (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
               )))
    POST [ tvoid ]
    EX c_final:Z, EX p_s_final:ptrofs, EX curr_head:val,
        PROP (
            Ptrofs.unsigned p_s_final = Z.add (Ptrofs.unsigned p_s_init) (Z.mul c_final PGSIZE) /\ 
            0 <= c_final /\ 
            (Ptrofs.unsigned p_s_final) <= (Ptrofs.unsigned p_n_init) /\ 
            (Ptrofs.unsigned p_n_init) < Z.add (Ptrofs.unsigned p_s_final) PGSIZE /\

            ((curr_head = original_freelist_pointer /\ c_final = 0) \/ (curr_head = (Vptr b_s_init (Ptrofs.sub p_s_final (Ptrofs.repr PGSIZE)))  /\ c_final <> 0))
            )
        RETURN ()
        SEP ((*denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_final (Ptrofs.repr PGSIZE))) (Vptr b_n_init p_n_init) &&*)
            if (0<?c_final) then
               (freelistrep sh (Nat.add (Z.to_nat c_final) n) (curr_head) *
               available_range sh (Vptr b_s_init p_s_final) (Vptr b_n_init p_n_init) PGSIZE *
               data_at sh t_struct_kmem (Vint (Int.repr xx), (curr_head)) (gv _kmem))
            else
            (((freelistrep sh n original_freelist_pointer)
            * (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
               ))

        ).

(************************ Gprog  *************************)
Definition Gprog : funspecs := [
   kfree1_freelist_spec;
   freerange_no_loop_no_add_spec;
   freerange_no_loop_no_add_1_spec;
   while_1_5_spec; freerange_while_loop_spec
].


(************************ Proofs  *************************)

(*Lemma body_kfree1_freelist': semax_body Vprog Gprog f_kfree1 kfree1_freelist_spec.
Proof. start_function. Intros. repeat forward. entailer. 
       induction n. 
       - assert (original_freelist_pointer = nullval). {
            rewrite <- H1; auto.
         }
         rewrite H7. unfold freelistrep. Exists nullval. entailer.
      - unfold freelistrep. Intros next_orig. Exists original_freelist_pointer. entailer.
         Exists next_orig. entailer. fold freelistrep. entailer!.
Qed.*)

Lemma body_kfree1_freelist: semax_body Vprog Gprog f_kfree1 kfree1_freelist_spec.
Proof. start_function. Intros. destruct number_structs eqn:en; try rep_lia. repeat forward. 
    entailer.
    induction n. 
    - assert (original_freelist_pointer = nullval). {
         rewrite <- H2; auto.
      }
      rewrite H11. unfold freelistrep. Exists nullval. fold available. 
      replace ((S n0) - 1)%nat with n0; try rep_lia.
      entailer!.
   - unfold freelistrep. Intros next_orig. Exists original_freelist_pointer. entailer.
      Exists next_orig. entailer. fold freelistrep. fold available. replace ((S n0) - 1)%nat with n0; try rep_lia. entailer!.
Qed.

(* freerange no loop is not updated with the newets kfreespec*)

(*Lemma body_freerange_no_loop_no_add: semax_body Vprog Gprog f_freerange_no_loop_no_add freerange_no_loop_no_add_spec.
Proof. start_function.
forward_if. 
   -apply andp_left1. entailer!.
   -forward_call (sh, new_head, original_freelist_pointer, xx, gv, n).
      +apply andp_left2. entailer!.
      +entailer. destruct (pointer_le_bool new_head pa_end) eqn:e; auto_contradict. 
         * entailer!. 
         * unfold pointer_le_bool in e.
           unfold pointer_cmp_bool in e. 
           unfold pointer_comparison in e.
           destruct (sem_cmp_pp Cle new_head pa_end) eqn:e1. 
           --destruct v; auto_contradict.
             apply typed_true_tint_Vint in H0.
             exfalso; apply H0.
             apply cmp_le_is_either_0_or_1 in e1. destruct e1; auto.
             rewrite H5 in e.
             simpl in e. inversion e.
           --entailer!.
   - forward. entailer. destruct (pointer_le_bool new_head pa_end) eqn:e1.
      + destruct (sem_cmp_pp Cle new_head pa_end ) eqn:e2; auto_contradict.
        destruct v; auto_contradict.
        apply typed_false_tint_Vint in H0.
        rewrite H0 in e2. unfold pointer_le_bool in e1. unfold pointer_cmp_bool in e1.
        unfold pointer_comparison in e1.
        rewrite e2 in e1. inversion e1.
      + apply andp_left2. entailer!.
Qed.*)

(*Lemma body_freerange_no_loop_no_add_1: semax_body Vprog Gprog f_freerange_no_loop_no_add_1 freerange_no_loop_no_add_1_spec.
Proof. start_function.
assert (sem_cmp_pp Cle
(Vptr b (Ptrofs.add p (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr PGSIZE))))) pa_end =
sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr PGSIZE)))) pa_end) by auto. 
assert (sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) pa_end =
sem_cmp_pp Cle (Vptr b (Ptrofs.add p
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr PGSIZE))))) pa_end
) by auto. 
forward_if. 
   - apply andp_left1. destruct pa_end; auto_contradict.
     entailer!. unfold denote_tc_test_order, PGSIZE. entailer!.
   -forward_call (sh, (Vptr b p), original_freelist_pointer, xx, gv, n).
      +apply andp_left2. entailer!.
      +entailer. destruct (pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) pa_end) eqn:e; auto_contradict. 
         *  entailer!. 
         * unfold pointer_le_bool in e.
           unfold pointer_cmp_bool in e. 
           unfold pointer_comparison in e.
           entailer. unfold PGSIZE in H1; rewrite <- H1 in H2. 
           destruct (sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) pa_end) eqn:e1; unfold PGSIZE in e1; rewrite e1 in H2. 
           --destruct v; auto_contradict.
             apply typed_true_tint_Vint in H2.
             exfalso; apply H2.
             apply cmp_le_is_either_0_or_1 in e1. destruct e1; auto.
             rewrite H7 in e.
             simpl in e. inversion e.
           --entailer!.
   - forward. entailer. destruct (pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) pa_end) eqn:e1.
      + destruct (sem_cmp_pp Cle
         (Vptr b
            (Ptrofs.add p
               (Ptrofs.mul (Ptrofs.repr 1)
                  (Ptrofs.of_ints (Int.repr 4096))))) pa_end)eqn:e2; auto_contradict.
         destruct v; auto_contradict.
         apply typed_false_tint_Vint in H2.

         rewrite H2 in e2. unfold pointer_le_bool in e1. unfold pointer_cmp_bool in e1.
        unfold pointer_comparison in e1.
        rewrite H1 in e1. unfold PGSIZE in e1. 
        rewrite e2 in e1. inversion e1.
      + apply andp_left2. entailer!.
Qed.*)

Lemma body_while_1_5: semax_body Vprog Gprog f_while_1_5 while_1_5_spec.
Proof. start_function. repeat forward.
forward_while
 (EX c_tmp: Z, EX p_s_tmp:ptrofs,
   PROP  (
    Ptrofs.unsigned p_s_tmp = Z.add (Ptrofs.unsigned p_s_init) (Z.mul c_tmp PGSIZE) /\ 
    0 <= c_tmp /\
    c_tmp <= Int.max_signed /\
    Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init
   )
   LOCAL (
    temp _c (Vint (Int.repr c_tmp));
    temp _pa_start (Vptr b_s_init p_s_tmp);
    temp _pa_end (Vptr b_n_init p_n_init)
    )
   SEP (denote_tc_test_order ((Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr (PGSIZE))))) (Vptr b_n_init p_n_init))).
   - repeat EExists; entailer. (* the precondition (of the whole loop) implies the loop invariant *)
   - entailer!. entailer. (* the loop-condition expression type-checks (i.e., guarantees to evaluate successfully) *)
   - repeat forward. (* the postcondition of the loop body implies the loop invariant *)
    +entailer!. apply c_tmp_bounds with (p_s_init:=p_s_init) (p_s_tmp:=p_s_tmp) (p_n_init:=p_n_init); try rep_lia. 
    + Exists (c_tmp + 1, Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)). entailer!.
        * split.
         -- destruct H as [H2 [H3 H4]].
         assert (Ptrofs.unsigned p_s_init + (c_tmp + 1) * PGSIZE = Ptrofs.unsigned p_s_init + (c_tmp) * PGSIZE + PGSIZE) as H; try rep_lia; rewrite H.
         assert (Ptrofs.unsigned p_s_init + c_tmp * PGSIZE + PGSIZE =  Ptrofs.unsigned p_s_tmp + PGSIZE) as H5; try rep_lia; rewrite H5.
         ptrofs_add_simpl_PGSIZE.
         -- repeat split_lia. 
                ++ apply c_tmp_bounds_max with (p_s_init:=p_s_init) (p_s_tmp:=p_s_tmp) (p_n_init:=p_n_init); try rep_lia.
                ++ apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init); unfold PGSIZE; auto.
        * entailer!. specialize (H0 p_s_tmp); apply H0. split_lia.
        destruct H1 as [H11 [H12 [H13 H14]]]. rewrite H11. apply Zle_left_rev.
        assert ( Ptrofs.unsigned p_s_init + c_tmp * PGSIZE + - Ptrofs.unsigned p_s_init =  Ptrofs.unsigned p_s_init + - Ptrofs.unsigned p_s_init + c_tmp * PGSIZE) by rep_lia. 
        rewrite H1. le_sub_self_add_and_solve.
    - forward. Exists c_tmp p_s_tmp. entailer!. split_lia. (* he loop invariant (and negation of the loop condition) is a strong enough precondition to prove the MORE-COMMANDS after the loop *)
        apply typed_false_offset_val_leq with (b_s_init:=b_s_init) (b_n_init:=b_n_init); try rep_lia; unfold PGSIZE; try rep_lia; auto.
Qed.


(** working in progress*)


Lemma body_freerange_while_loop_spec: semax_body Vprog Gprog f_freerange_while_loop freerange_while_loop_spec.
Proof. start_function. 
forward_while
 (EX c_tmp: Z, EX p_s_tmp:ptrofs, EX curr_head:val,
   PROP  (
    Ptrofs.unsigned p_s_tmp = Z.add (Ptrofs.unsigned p_s_init) (Z.mul c_tmp PGSIZE) /\ 
    0 <= c_tmp /\
    c_tmp <= Int.max_signed /\
    Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init /\
    ((curr_head = original_freelist_pointer /\ c_tmp = 0) \/ (curr_head = (Vptr b_s_init (Ptrofs.sub p_s_tmp (Ptrofs.repr PGSIZE)))  /\ c_tmp <> 0))
   )
   LOCAL (
      gvars gv;
      temp _pa_start (Vptr b_s_init p_s_tmp);
      temp _pa_end (Vptr b_n_init p_n_init)
    ) 
   SEP (
      ensure_comparable_range sh (Vptr b_s_init p_s_init) (Vptr b_n_init p_n_init) PGSIZE  &&
      (freelistrep sh (Nat.add (Z.to_nat c_tmp) n) (curr_head) *
      available_range sh (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) PGSIZE *
      data_at sh t_struct_kmem (Vint (Int.repr xx), curr_head) (gv _kmem))
      )
  )%assert.
   - Exists 0 p_s_init original_freelist_pointer. entailer. 
   - entailer. apply andp_left1. entailer. apply ensure_comparable_range_arbitrary with (c:=c_tmp); try rep_lia. destruct H0; unfold PGSIZE; auto.
   - forward_call (sh, (Vptr b_s_init p_s_tmp), curr_head, xx, gv, (Nat.add (Z.to_nat c_tmp) n), PGSIZE, (Z.to_nat (compute_c (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) PGSIZE))).
      + apply andp_left2. sep_apply available_range_correct. entailer!.
      + destruct H as [H1 [H2 [H3 [H4 H5]]]]; destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; split; auto.
         split.
         * destruct H05; subst; simpl; try rep_lia; auto. destruct c_tmp eqn:ec; try rep_lia; auto_contradict; destruct H; rewrite H; auto. destruct H; unfold is_pointer_or_null; rewrite H; auto.
         * apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto. 
         unfold compute_c. destruct (PGSIZE <=? 0) eqn:e1; unfold PGSIZE in e1; auto_contradict.
         rewrite e1. destruct (Ptrofs.ltu p_n_init p_s_tmp) eqn:e2.
         -- unfold Ptrofs.ltu in e2. destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned p_s_tmp)) eqn:e3; auto_contradict.
            assert (Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init). { apply Z.le_trans with (m:= Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE))); unfold PGSIZE; try rep_lia. }
            rep_lia.
         -- assert (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)) = Ptrofs.unsigned p_s_tmp + PGSIZE) by ptrofs_add_simpl_PGSIZE.
            unfold PGSIZE in H; rewrite H in HRE.
            assert (PGSIZE <= Ptrofs.unsigned p_n_init - Ptrofs.unsigned p_s_tmp) by (rewrite <- Z.le_add_le_sub_l; auto). 
            assert ((PGSIZE / PGSIZE) <= ((Ptrofs.unsigned p_n_init - Ptrofs.unsigned p_s_tmp) / PGSIZE)) by (apply Z.div_le_lower_bound; unfold PGSIZE; try rep_lia; auto). 
            replace (PGSIZE / PGSIZE) with 1 in H6; auto.
            unfold Nat.le; assert ((1)%nat = Z.to_nat 1); auto; rewrite H7; apply Z_to_nat_monotone; auto.
      + Intros. forward. Exists (c_tmp + 1, Ptrofs.add p_s_tmp (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tschar)) (ptrofs_of_int Signed (Int.repr PGSIZE))), Vptr b_s_init p_s_tmp). (* Vptr b_s_init p_s_tmp is current head*)
        entailer!. 
        * repeat split_lia.
         -- destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite ptrofs_add_simpl; simplify_signed_PGSIZE.
            ++ rewrite H01.
            assert ((c_tmp * PGSIZE + PGSIZE) = ((c_tmp+1) * PGSIZE)%Z); try rep_lia.
            unfold PGSIZE in H0 at 2. try rep_lia. 
            ++ split; try rep_lia.
            apply Z.le_lt_trans with (m := Int.max_signed); try rep_lia.
            apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.
            apply Z.le_trans with (m := Ptrofs.unsigned p_n_init + PGSIZE); try rep_lia.
            unfold PGSIZE; try rep_lia.
         -- apply c_tmp_bounds_max with (p_s_init:=p_s_init) (p_s_tmp:=p_s_tmp) (p_n_init:=p_n_init); try rep_lia.
         -- rewrite ptrofs_add_simpl; try rep_lia.
            ++ apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.
               rewrite ptrofs_add_simpl in HRE; try rep_lia.   
               ** simplify_signed_PGSIZE. 
               ** (* this is the almost the same as above.. *)  split; try rep_lia.
               apply Z.le_lt_trans with (m := Int.max_signed); try rep_lia.
               (*apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.*)
               apply Z.le_trans with (m := Ptrofs.unsigned p_n_init + PGSIZE); try rep_lia.
               unfold PGSIZE; try rep_lia.
            ++ split; try rep_lia. simplify_signed_PGSIZE.
            ++ (** this is the same as above*)simplify_signed_PGSIZE; split_lia. apply Z.le_lt_trans with (m := Int.max_signed); try rep_lia.
               (*apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.*)
               apply Z.le_trans with (m := Ptrofs.unsigned p_n_init + PGSIZE); try rep_lia.
               unfold PGSIZE; try rep_lia.
         -- destruct H0 as [H01 [H02 [H03 [H04 H05]]]].
            right.
            replace (Ptrofs.repr (Int.signed (Int.repr PGSIZE))) with (Ptrofs.repr PGSIZE) by auto.
            assert ((Ptrofs.sub (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)) (Ptrofs.repr PGSIZE)) = p_s_tmp). {
               rewrite Ptrofs.sub_add_opp. rewrite Ptrofs.add_assoc. rewrite Ptrofs.add_neg_zero.
               apply Ptrofs.add_zero.
            }
            rewrite H0; auto. 
            split; auto; rep_lia.
        * apply andp_right.
         --  admit. (* ensure comparable*)
         -- assert (S (Z.to_nat c_tmp + n) = (Z.to_nat (c_tmp + 1) + n)%nat) by rep_lia.
            rewrite H7. entailer!.
            unfold available_range.
            destruct (sameblock (Vptr b_s_init
                  (Ptrofs.add p_s_tmp (Ptrofs.repr (Int.signed (Int.repr PGSIZE)))))
               (Vptr b_n_init p_n_init)) eqn:eb.
            ++ replace (Ptrofs.repr (Int.signed (Int.repr PGSIZE))) with (Ptrofs.repr PGSIZE) by auto.
               unfold add_offset.
               unfold compute_c; destruct (PGSIZE <=? 0) eqn:ep; auto_contradict.
               unfold Ptrofs.ltu. destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned p_s_tmp)) eqn:e1.
               ** try rep_lia. 
               ** destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))) eqn:e2.
                  --- assert ((Ptrofs.unsigned p_n_init - (Ptrofs.unsigned p_s_tmp + PGSIZE)) / PGSIZE = 0). {
                     apply Zdiv_small; apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE. split.
                     +++ apply Zle_minus_le_0.
                        rewrite <- ptrofs_add_simpl; auto; unfold PGSIZE; try rep_lia.
                     +++ unfold PGSIZE in l. rep_lia. 
                     }
                     assert((Ptrofs.unsigned p_n_init - (Ptrofs.unsigned p_s_tmp + PGSIZE)) = PGSIZE * ((Ptrofs.unsigned p_n_init - (Ptrofs.unsigned p_s_tmp + PGSIZE))/PGSIZE) + ((Ptrofs.unsigned p_n_init - (Ptrofs.unsigned p_s_tmp + PGSIZE)) mod PGSIZE)). {
                        apply Z.div_mod; rep_lia.
                     }
                     (*rewrite H10 in H11. rewrite Z.mul_0_r in H11. rewrite Z.add_0_l in H11.*)
                    (* rewrite <- Zminus_mod_idemp_r in H11. rewrite <- Zplus_mod_idemp_r in H11.
                     rewrite Z_mod_same_full in H11. rewrite Z.add_0_r in H11. rewrite Zminus_mod_idemp_r in H11.
                     assert (Ptrofs.unsigned p_n_init - (Ptrofs.unsigned p_s_tmp) =
                                 (PGSIZE * ((Ptrofs.unsigned p_n_init - (Ptrofs.unsigned p_s_tmp + PGSIZE)) / PGSIZE) +
                                 (Ptrofs.unsigned p_n_init - Ptrofs.unsigned p_s_tmp) mod PGSIZE) + PGSIZE). {
                                 symmetry. 
                                 rewrite Zeq_plus_swap. rewrite <- H11. try rep_lia.
                                 }*)
                                 
                     assert ((Ptrofs.unsigned p_n_init - (Ptrofs.unsigned p_s_tmp)) / PGSIZE = 1). {
                        admit.
                     }
                     rewrite H12. simpl. entailer!.
                  --- assert ((Z.to_nat ((Ptrofs.unsigned p_n_init - Ptrofs.unsigned p_s_tmp) / PGSIZE) - 1)%nat = (Z.to_nat ((Ptrofs.unsigned p_n_init -
                           Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE))) / PGSIZE))). {
                              admit. (* arithmetics *)
                           }
                           rewrite H10. entailer!.
            ++ apply sameblock_false in eb. apply typed_true_same_block in HRE; auto_contradict.
   - forward. Exists c_tmp p_s_tmp curr_head. entailer!. (* the loop invariant (and negation of the loop condition) is a strong enough precondition to prove the MORE-COMMANDS after the loop *)
            ++ split_lia. 
               apply typed_false_offset_val_leq with (b_s_init:=b_s_init) (b_n_init:=b_n_init); try rep_lia; unfold PGSIZE; try rep_lia; auto.
               destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; auto.
            ++ apply andp_left2. destruct (0 <? c_tmp) eqn:ec.
            --- destruct H0 as [H01 [H02 [H03 [H04 H05]]]].
                  destruct H05; destruct H0.
                  +++ rewrite H1 in ec. auto_contradict.
                  +++ subst. entailer. (*DER ER STADIG PROBLEMER MED HOVEDET...*)
            --- destruct H0 as [H01 [H02 [H03 [H04 H05]]]];  assert (0 = c_tmp); try rep_lia.
               destruct H05.
               +++ destruct H1; rewrite H1. replace (Z.to_nat (c_tmp) + n)%nat with n; try rep_lia.
                     sep_apply available_range_correct. unfold compute_c. 
                     destruct (PGSIZE <=? 0) eqn:e1; auto_contradict.
                     unfold Ptrofs.ltu.
                     destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned p_s_tmp)) eqn:e2.
               *** simpl; entailer!.
               *** apply typed_false_offset_val_leq with (b_s_init:=b_s_init) (b_n_init:=b_n_init) in HRE; try rep_lia.
                     rewrite <- Z.lt_sub_lt_add_l in HRE.  
                     assert ((Ptrofs.unsigned p_n_init - Ptrofs.unsigned p_s_tmp) / PGSIZE = 0). { apply Zdiv_small. split; try rep_lia; auto. }
                     rewrite H3. simpl. entailer!.
               +++ destruct H1; rewrite H0 in H2; auto_contradict.
Admitted.
            
        