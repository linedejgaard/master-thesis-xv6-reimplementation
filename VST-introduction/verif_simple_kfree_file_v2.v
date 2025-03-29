Require Import VST.floyd.proofauto.
Require Import VC.simple_kfree_file.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_run := Tstruct _run noattr.

Definition t_struct_kmem := Tstruct _struct_kmem noattr.

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
        !! malloc_compatible (sizeof t_run) p &&  (* p is compatible with a memory block of size sizeof theader. *)
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
   freelistrep Ews n p |-- valid_pointer p.
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
          !! (n = S m) && !! malloc_compatible (sizeof t_run) x && data_at sh t_run next x * freelistrep sh m next.
Proof.
   intros; apply pred_ext.
   - destruct n. 
         + unfold freelistrep. entailer!.
         + unfold freelistrep; fold freelistrep. Intros y.
         Exists n y. entailer!.
   - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. Exists y. entailer!.
Qed.

Definition kfree1_freelist_spec := 
   DECLARE _kfree1
      WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat
      PRE [ tptr tvoid]
         PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) 
         PARAMS (new_head) GLOBALS(gv)
         SEP (
            freelistrep sh n original_freelist_pointer *
            (!! malloc_compatible (sizeof t_run) new_head &&
            data_at sh (t_run) nullval new_head *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) )
         )
      POST [ tvoid ]
         PROP()
         RETURN () 
         SEP (
            freelistrep sh (S n) new_head *
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
            (!! malloc_compatible (sizeof t_run) new_head &&
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
               (!! malloc_compatible (sizeof t_run) new_head &&
               data_at sh (t_run) nullval new_head *
               data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) )
         ).

(************** pointer comparison add + call **************'*)
Definition PGSIZE : Z := 4096. 

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
            (!! malloc_compatible (sizeof t_run) (Vptr b p) &&
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
               (!! malloc_compatible (sizeof t_run) (Vptr b p) &&
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
         denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_init (Ptrofs.repr PGSIZE)))
                                  (Vptr b_n_init p_n_init) &&
         (!! (forall p_s_tmp,
         Ptrofs.unsigned p_s_init <= Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init ->
         ((denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))
         (Vptr b_n_init p_n_init)) |--
            (denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr (PGSIZE + PGSIZE))))
                                  (Vptr b_n_init p_n_init)))
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


(************************ Gprog  *************************)
Definition Gprog : funspecs := [
   kfree1_freelist_spec;
   freerange_no_loop_no_add_spec;
   freerange_no_loop_no_add_1_spec;
   while_1_5_spec (*; freerange_while_loop_spec*)
].

(************************ Helper functions and tactics  *************************)

Ltac auto_contradict := try discriminate; try contradiction.
Ltac split_lia := split; try rep_lia.

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

Ltac rep_lia_PGSIZE := unfold PGSIZE; rep_lia.

(*Lemma ptrofs_add_simpl_PGSIZE :
  forall a,
    0 <= Ptrofs.unsigned a + PGSIZE < Ptrofs.modulus ->
    Ptrofs.unsigned (Ptrofs.add a (Ptrofs.repr PGSIZE)) =
    Ptrofs.unsigned a + PGSIZE.
Proof.
   intros. apply ptrofs_add_simpl; try rep_lia; unfold PGSIZE; try rep_lia.
Qed.*)

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
   destruct (sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) (* find a solution for magic number 4096 *)
   (Vptr b_n_init p_n_init)) eqn:e; auto_contradict.
   destruct v; auto_contradict.
   assert (i = Int.zero \/ i = Int.one). { apply cmp_le_is_either_0_or_1 with (p:= (offset_val ofs (Vptr b_s_init p_s_tmp))) (q:=(Vptr b_n_init p_n_init) ); auto. }
   destruct H; auto_contradict.
   ** subst; auto_contradict.
   ** rewrite H in e. 
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
   destruct (sem_cmp_pp Cle (offset_val ofs (Vptr b_s_init p_s_tmp)) (* find a solution for magic number 4096 *)
   (Vptr b_n_init p_n_init)) eqn:e; auto_contradict.
   destruct v; auto_contradict.
   assert (i = Int.zero \/ i = Int.one). { apply cmp_le_is_either_0_or_1 with (p:= (offset_val PGSIZE (Vptr b_s_init p_s_tmp))) (q:=(Vptr b_n_init p_n_init) ); auto. }
   destruct H.
   2: { subst. auto_contradict. }
   subst. unfold sem_cmp_pp in e. simpl in e. destruct (eq_block b_s_init b_n_init); auto_contradict.
   destruct ((Some (negb (Ptrofs.ltu p_n_init (Ptrofs.add p_s_tmp (Ptrofs.repr ofs)))))) eqn:e1; auto_contradict.
   destruct b; auto_contradict.
   unfold negb in e1; unfold Ptrofs.ltu in e1. destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr ofs)))) eqn:e2; auto_contradict.
   intros.
   assert (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr ofs)) = Ptrofs.unsigned p_s_tmp + ofs). {
      apply ptrofs_add_simpl; split_lia. (*apply Z.add_nonneg_nonneg; unfold ofs; try rep_lia.*)
   }
   rewrite <- H2. unfold PGSIZE; apply l.
Admitted.

(************************ Proofs  *************************)

Lemma body_kfree1_freelist': semax_body Vprog Gprog f_kfree1 kfree1_freelist_spec.
Proof. start_function. Intros. repeat forward. entailer. 
       induction n. 
       - assert (original_freelist_pointer = nullval). {
            rewrite <- H1; auto.
         }
         rewrite H7. unfold freelistrep. Exists nullval. entailer.
      - unfold freelistrep. Intros next_orig. Exists original_freelist_pointer. entailer.
         Exists next_orig. entailer. fold freelistrep. entailer!.
Qed.

Lemma body_freerange_no_loop_no_add: semax_body Vprog Gprog f_freerange_no_loop_no_add freerange_no_loop_no_add_spec.
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
Qed.

Lemma body_freerange_no_loop_no_add_1: semax_body Vprog Gprog f_freerange_no_loop_no_add_1 freerange_no_loop_no_add_1_spec.
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
Qed.

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

   - repeat EExists; entailer.
   - entailer!. entailer.
   - repeat forward. 
    +entailer!. apply c_tmp_bounds with (p_s_init:=p_s_init) (p_s_tmp:=p_s_tmp) (p_n_init:=p_n_init); try rep_lia. 
    + Exists (c_tmp + 1, Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)). entailer!.
        * split.
         -- destruct H as [H2 [H3 H4]].
         assert (Ptrofs.unsigned p_s_init + (c_tmp + 1) * PGSIZE = Ptrofs.unsigned p_s_init + (c_tmp) * PGSIZE + PGSIZE) as H; try rep_lia; rewrite H.
         assert (Ptrofs.unsigned p_s_init + c_tmp * PGSIZE + PGSIZE =  Ptrofs.unsigned p_s_tmp + PGSIZE) as H5; try rep_lia; rewrite H5.
         apply ptrofs_add_simpl; split_lia; rep_lia_PGSIZE.
         -- repeat split_lia. 
                ++ apply c_tmp_bounds_max with (p_s_init:=p_s_init) (p_s_tmp:=p_s_tmp) (p_n_init:=p_n_init); try rep_lia.
                ++ apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init); unfold PGSIZE; auto.
        * entailer!. specialize (H0 p_s_tmp); apply H0. split_lia.
        destruct H1 as [H11 [H12 [H13 H14]]]. rewrite H11. apply Zle_left_rev.
        assert ( Ptrofs.unsigned p_s_init + c_tmp * PGSIZE + - Ptrofs.unsigned p_s_init =  Ptrofs.unsigned p_s_init + - Ptrofs.unsigned p_s_init + c_tmp * PGSIZE) by rep_lia. 
        rewrite H1. assert (Ptrofs.unsigned p_s_init + - Ptrofs.unsigned p_s_init = 0) by rep_lia.
        apply Z.add_nonneg_nonneg; unfold PGSIZE; rep_lia.
    - forward. Exists c_tmp p_s_tmp. entailer!. split_lia.
        
        destruct (sem_cmp_pp Cle (offset_val 4096 (Vptr b_s_init p_s_tmp)) (* find a solution for magic number 4096 *)
        (Vptr b_n_init p_n_init)) eqn:e; auto_contradict.
        destruct v; auto_contradict.
        assert (i = Int.zero \/ i = Int.one). { apply cmp_le_is_either_0_or_1 with (p:= (offset_val PGSIZE (Vptr b_s_init p_s_tmp))) (q:=(Vptr b_n_init p_n_init) ); auto. }
        destruct H2.
        2: { subst. auto_contradict. }
        subst.
        unfold sem_cmp_pp in e. simpl in e. destruct (eq_block b_s_init b_n_init); auto_contradict.
        destruct ((Some (negb (Ptrofs.ltu p_n_init (Ptrofs.add p_s_tmp (Ptrofs.repr 4096)))))) eqn:e1; auto_contradict.
        destruct b; auto_contradict.
        unfold negb in e1; unfold Ptrofs.ltu in e1. destruct (zlt (Ptrofs.unsigned p_n_init) (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr 4096)))) eqn:e2; auto_contradict.
        assert (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)) = Ptrofs.unsigned p_s_tmp + PGSIZE). {
            apply ptrofs_add_simpl; split_lia; rep_lia_PGSIZE. (*apply Z.add_nonneg_nonneg; unfold PGSIZE; try rep_lia.*)
        }
        rewrite <- H2. unfold PGSIZE; apply l.
Qed.
