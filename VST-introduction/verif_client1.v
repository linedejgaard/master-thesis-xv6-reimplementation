Require Import VST.floyd.proofauto.
Require Import VC.client1.
Require Import VC.helper.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(************************ freelistrep *********************************)
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


(************************ specs *********************************)
Definition kfree1_spec := 
    DECLARE _kfree1
       WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, size:Z, number_structs_available:nat
       PRE [ tptr tvoid]
          PROP(
               writable_share sh /\
               is_pointer_or_null original_freelist_pointer /\
               (Nat.le (S O) (number_structs_available) ) (* there is at least one available *)
               ) 
          PARAMS (new_head) GLOBALS(gv)
          SEP (
             freelistrep sh n original_freelist_pointer *
             available sh number_structs_available new_head PGSIZE *
             (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) )
          )
       POST [ tvoid ]
          PROP(isptr new_head)
          RETURN () 
          SEP (
             freelistrep sh (S n) new_head *
             available sh (Nat.sub number_structs_available (S O)) (add_offset new_head PGSIZE) PGSIZE *
             data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
             ).

Definition kalloc1_spec := (* this doesn't assume that the list is empty, but that q is either a pointer or a nullval *)
DECLARE _kalloc1
WITH sh : share, original_freelist_pointer:val, xx:Z, n:nat, gv:globals
PRE [ ]
    PROP(writable_share sh /\ 
        ((Nat.eq O n /\ original_freelist_pointer = nullval) \/ (Nat.lt O n /\ isptr original_freelist_pointer))
    ) 
    PARAMS () GLOBALS(gv)
    SEP (
        freelistrep sh n original_freelist_pointer * (* TODO: fix this.. *)
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)) (* q can be nullval meaning that there is only one run *)
POST [ tptr tvoid ]
    PROP()
    RETURN (original_freelist_pointer) (* we return the head like in the pop function*)
    SEP (
        if (eq_dec original_freelist_pointer nullval) then
        (
            (*data_at sh t_run next original_freelist_pointer **)
            freelistrep sh n original_freelist_pointer * (* TODO: fix this.. *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* q can be nullval meaning that there is only one run *)
        )
        else 
            (
                EX next,
                data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                freelistrep sh (Nat.sub n (S O)) next *
                data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
            )
        ).


Definition client1_spec := (* kind of pop *)
DECLARE _client1
WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, next:val, number_structs_available:nat
PRE [ tptr tvoid ]
    PROP(
        writable_share sh /\
        is_pointer_or_null new_head /\
        (*is_pointer_or_null original_freelist_pointer /\*)
        (Nat.le (S O) number_structs_available) /\

        ((Nat.eq O n /\ original_freelist_pointer = nullval) \/ (Nat.lt O n /\ isptr original_freelist_pointer))
    ) 
    PARAMS (new_head) GLOBALS(gv)
    SEP (
        freelistrep sh n original_freelist_pointer *
        available sh number_structs_available new_head PGSIZE *
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
    )
POST [ tptr tvoid ]
    PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            EX next, (* ideally, I would like to have that next was the original freelist*)
            data_at sh t_run next new_head *
            available sh (number_structs_available - 1) (add_offset new_head PGSIZE) PGSIZE *
            freelistrep sh n next *
            data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
            ).

(************************ Gprog  *************************)

Definition Gprog : funspecs := [
    kfree1_spec; 
    kalloc1_spec; 
    client1_spec
].

(************************ Proofs  *************************)
Lemma body_kfree1: semax_body Vprog Gprog f_kfree1 kfree1_spec.
Proof. start_function. Intros. destruct number_structs_available eqn:en; try rep_lia. destruct H. repeat forward. 
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

Lemma body_kalloc1: semax_body Vprog Gprog f_kalloc1 kalloc1_spec.
Proof. start_function. Intros. destruct H; forward. (*unfold abbreviate in POSTCONDITION. *)
forward_if (
   
    PROP  (
        (*r <> nullval*)
    )
    LOCAL (
        temp _r original_freelist_pointer; 
        gvars gv
        )
    SEP (
        if (eq_dec original_freelist_pointer nullval) then
        (
            freelistrep sh n original_freelist_pointer * (* TODO: fix this.. *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* q can be nullval meaning that there is only one run *)
        )
        else 
            (
                EX next,
                data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                freelistrep sh (Nat.sub n (S O)) next *
                data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
            )
    )
)%assert.
- destruct n eqn:en; destruct H0 as [[H011 H012] | [H021 H022]]. (* original free list pointer is different from null *)
    + rewrite H012 in H1; auto_contradict.
    + unfold Nat.lt in H021; rep_lia.
    + rewrite H012 in H1; auto_contradict.
    + unfold freelistrep; fold freelistrep. Intros next. 
        repeat forward. (*Exists next.*)
        destruct (eq_dec original_freelist_pointer nullval) eqn:eofln; entailer!.
        Exists next.
        assert ((S n0 - 1)%nat = n0); try rep_lia.
        rewrite H8; entailer.
- destruct n eqn:en. (* original freelist pointer is null *)
    + destruct H0 as [[H011 H012] | [H021 H022]]; forward; destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict; entailer. 
    + destruct H0 as [[H011 H012] | [H021 H022]]; try (unfold Nat.lt in H011; rep_lia).
        forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict.
        entailer.
- destruct n eqn:en.
    + destruct H0 as [[H011 H012] | [H021 H022]].
        * destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. forward.
        * unfold Nat.lt in H021; try rep_lia.
    + destruct H0 as [[H011 H012] | [H021 H022]].
        * destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict.
        * destruct (eq_dec original_freelist_pointer nullval) eqn:e1.
            -- rewrite e in H022. auto_contradict.
            -- forward.
Qed.


Lemma body_client1: semax_body Vprog Gprog f_client1 client1_spec.
Proof.
start_function.
forward_call (sh, new_head, original_freelist_pointer, xx, gv, n, PGSIZE, number_structs_available). (* call kfree1 *)
- destruct H as [H1 [H2 [H3 H4]]]; split; auto. destruct H4.
    + destruct H. rewrite H0. unfold is_pointer_or_null; unfold nullval; simpl; auto.
    + destruct H. destruct original_freelist_pointer; auto_contradict. unfold is_pointer_or_null; auto.
- (*unfold abbreviate in POSTCONDITION.*) forward_call (sh, new_head, xx, (S n), gv). (* call kfree1 *)
    + entailer!. 
    + destruct H as [H1 [H2 [H3 [[H411 H412] | [H421 H422]]]]]; split; auto.
        * right; split; auto; try rep_lia.
        * right; split; auto; try rep_lia.
    + destruct (eq_dec new_head nullval) eqn:enh.
        * rewrite e in H0; auto_contradict.
        * forward. Exists x. entailer!. assert ((S n - 1)%nat = n); try rep_lia. rewrite H10. entailer!.
Qed.