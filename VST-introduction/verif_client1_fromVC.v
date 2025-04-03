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
          !! (n = S m) && !! malloc_compatible (sizeof t_run) x && data_at sh t_run next x * freelistrep sh m next.
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
               (Nat.le (S O) (number_structs_available) )  /\ 
               isptr new_head
               ) 
          PARAMS (new_head) GLOBALS(gv)
          SEP (
                freelistrep sh n original_freelist_pointer *
                available sh number_structs_available new_head PGSIZE *
                (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
             )
          )
       POST [ tvoid ]
          PROP(isptr new_head)
          RETURN () 
          SEP (
             !! malloc_compatible (sizeof t_run) new_head && 
             data_at sh t_run original_freelist_pointer new_head * 
             freelistrep sh n original_freelist_pointer *
             available sh (Nat.sub number_structs_available (S O)) (add_offset new_head PGSIZE) PGSIZE *
             data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
             ).

Definition kalloc1_spec :=
DECLARE _kalloc1
WITH sh : share, original_freelist_pointer:val, xx:Z, n:nat, next:val, gv:globals
PRE [ ]
    PROP(writable_share sh /\ 
        ((Nat.eq O n /\ original_freelist_pointer = nullval) \/ (Nat.lt O n /\ isptr original_freelist_pointer))
    ) 
    PARAMS () GLOBALS(gv)
    SEP (
        if (eq_dec original_freelist_pointer nullval) then
            (
                freelistrep sh n original_freelist_pointer * (* TODO: fix this.. *)
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
            ) (* q can be nullval meaning that there is only one run *)
        else 
            (
                !! malloc_compatible (sizeof t_run) original_freelist_pointer && 
                data_at sh t_run next original_freelist_pointer * 
                freelistrep sh (Nat.sub n (S O)) next *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
            )
        )  
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
                data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                freelistrep sh (Nat.sub n (S O)) next *
                data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
            )
        ).


Definition client1_spec := 
DECLARE _client1
WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, next:val, number_structs_available:nat
PRE [ tptr tvoid ]
    PROP(
        writable_share sh /\
        isptr new_head /\
        (Nat.le (S O) number_structs_available) /\
        ((Nat.eq O n /\ original_freelist_pointer = nullval) \/ (Nat.lt O n /\ isptr original_freelist_pointer))
    ) 
    PARAMS (new_head) GLOBALS(gv)
    SEP (
        (EX v, data_at sh t_run v new_head) *
        freelistrep sh n original_freelist_pointer *
        available sh number_structs_available new_head PGSIZE *
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
    )
POST [ tptr tvoid ]
    PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            data_at sh t_run original_freelist_pointer new_head *
            available sh (number_structs_available - 1) (add_offset new_head PGSIZE) PGSIZE *
            freelistrep sh n original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
            ).

(*Definition client2_spec := 
    DECLARE _client2
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, next:val, number_structs_available:nat
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            (Nat.le (S (S O)) number_structs_available) /\
            ((Nat.eq O n /\ original_freelist_pointer = nullval) \/ (Nat.lt O n /\ isptr original_freelist_pointer))
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            freelistrep sh n original_freelist_pointer *
            available sh number_structs_available pa1 PGSIZE *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP (
                data_at sh t_run original_freelist_pointer pa1 *
                available sh (number_structs_available - 1) (add_offset pa1 PGSIZE) PGSIZE *
                freelistrep sh n original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).

Definition client3_spec := 
    DECLARE _client3
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, next:val, number_structs_available:nat
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            (Nat.le (S (S O)) number_structs_available) /\
            ((Nat.eq O n /\ original_freelist_pointer = nullval) \/ (Nat.lt O n /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            freelistrep sh n original_freelist_pointer *
            available sh number_structs_available pa1 PGSIZE *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP (
                if (eq_dec pa1 nullval) then
                    (
                        if (eq_dec pa2 nullval) then 
                            (available sh (number_structs_available - 1) (add_offset pa1 PGSIZE) PGSIZE *
                            freelistrep sh n original_freelist_pointer *
                            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
                        else 
                            (data_at sh t_run original_freelist_pointer pa2 *
                            ((available sh (number_structs_available - 1) (add_offset pa1 PGSIZE) PGSIZE *
                            freelistrep sh n original_freelist_pointer *
                            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))))
                    )
                else 
                (
                    data_at sh t_run original_freelist_pointer pa1 *
                    (if (eq_dec pa2 nullval) then 
                            (available sh (number_structs_available - 1) (add_offset pa1 PGSIZE) PGSIZE *
                            freelistrep sh n original_freelist_pointer *
                            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
                        else 
                            (data_at sh t_run original_freelist_pointer pa2 *
                            ((available sh (number_structs_available - 1) (add_offset pa1 PGSIZE) PGSIZE *
                            freelistrep sh n original_freelist_pointer *
                            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)))))
                )
                ).*)

Definition client4_spec := 
    DECLARE _client4
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, next:val, number_structs_available:nat
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            (Nat.le (S (S O)) number_structs_available) /\
            ((Nat.eq O n /\ original_freelist_pointer = nullval) \/ (Nat.lt O n /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            freelistrep sh n original_freelist_pointer *
            available sh number_structs_available pa1 PGSIZE *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run original_freelist_pointer pa2 *
                available sh (number_structs_available - 1) (add_offset pa2 PGSIZE) PGSIZE *
                freelistrep sh n original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).

(************************ Gprog  *************************)

Definition Gprog : funspecs := [
    kfree1_spec; 
    kalloc1_spec; 
    client1_spec;
    (*client2_spec;
    client3_spec;*)
    client4_spec
].

(************************ Proofs  *************************)
Lemma body_kfree1: semax_body Vprog Gprog f_kfree1 kfree1_spec.
Proof. start_function. Intros. destruct number_structs_available eqn:en; try rep_lia. destruct H. repeat forward. 
    entailer. fold available.
    induction n. 
    - assert (original_freelist_pointer = nullval). {
         rewrite <- H2; auto.
      }
      (*rewrite H11.*) unfold freelistrep.
      rewrite S_pred.
      entailer.
   - rewrite S_pred. entailer!. 
Qed.

Lemma body_kalloc1: semax_body Vprog Gprog f_kalloc1 kalloc1_spec.
Proof. start_function. 
destruct (eq_dec original_freelist_pointer nullval) eqn:eofln.
-destruct H as [H0 [[H011 H012] | [H021 H022]]];
    Intros; forward;
        forward_if (
            PROP  ( )
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
                        data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                        freelistrep sh (Nat.sub n (S O)) next *
                        data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
                    )
            )
        )%assert; 
    try (rewrite H012 in H; auto_contradict).
    + forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.
    + destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. forward.
    + rewrite e in H; auto_contradict.
    + forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.
    + destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. forward.
- Intros. unfold Nat.eq, Nat.lt in H; destruct n eqn:en; auto_contradict;
    destruct H as [H1 [[H211 H212] | [H221 H222]]]; auto_contradict; try rep_lia.
    forward.
    forward_if (
        PROP  ( )
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
                    (*EX next,*)
                    data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                    freelistrep sh (Nat.sub n (S O)) next *
                    data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
                )
        )
    )%assert.
    + repeat forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer.
    entailer.
    + forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict.
    + forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict.
    entailer!.
Qed.

Lemma body_client1: semax_body Vprog Gprog f_client1 client1_spec.
Proof.
start_function.
forward_call (sh, new_head, original_freelist_pointer, xx, gv, n, PGSIZE, number_structs_available). (* call kfree1 *)
- destruct H as [H1 [H2 [H3 H4]]]; split; auto; destruct H4.
    + destruct H. split; auto. rewrite H0. unfold is_pointer_or_null; unfold nullval; simpl; auto. 
    + destruct H. split; auto. (*destruct original_freelist_pointer; auto_contradict. unfold is_pointer_or_null; auto.*)
- forward_call (sh, new_head, xx, (S n), original_freelist_pointer, gv). (* call kalloc *)
    + entailer. unfold freelistrep; fold freelistrep.
        destruct (eq_dec new_head nullval) eqn:enh.
        * subst; auto_contradict.
        * rewrite S_pred. entailer!. 
    + destruct H as [H1 [H2 [H3 [[H411 H412] | [H421 H422]]]]]; split; auto.
        * right; split; auto; try rep_lia.
        * right; split; auto; try rep_lia.
    + destruct (eq_dec new_head nullval) eqn:enh.
        * rewrite e in H0; auto_contradict.
        * forward. rewrite S_pred. entailer!.
Qed.

(*Lemma body_client2: semax_body Vprog Gprog f_client2 client2_spec.
Proof.
start_function.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, n, PGSIZE, number_structs_available). (* call kfree1 *)
- destruct H as [H1 [H2 [H3 H4]]]; split; auto. destruct H4; destruct H; auto.
    + rewrite H0; unfold is_pointer_or_null; simpl; auto; split; auto. 
    (*+ destruct H. rewrite H0. unfold is_pointer_or_null; unfold nullval; simpl; auto.
    + destruct H. destruct original_freelist_pointer; auto_contradict. unfold is_pointer_or_null; auto.*)
- forward_call (sh, pa2, pa1, xx, gv, S n, PGSIZE, (number_structs_available -1)%nat). (* call kfree1 *)
    + entailer.
    unfold freelistrep at 2; fold freelistrep. Exists original_freelist_pointer. entailer!.
    admit. (* fix available..*)
    + destruct H; auto.
    + forward_call (sh, pa2, xx, (S (S n)), pa1, gv). (* call kalloc 1 *)
        * entailer.
        * entailer.
        * split; destruct H; auto.
        right. split; auto. unfold Nat.lt; try rep_lia.
        * destruct (eq_dec pa2 nullval).
            -- rewrite e in H1; auto_contradict.
            -- forward_call (sh, pa1, xx, (S n), original_freelist_pointer, gv).
                ++ destruct (eq_dec pa1 nullval).
                    ** rewrite e in H0. auto_contradict.
                    ** entailer.
                ++ destruct (eq_dec pa1 nullval).
                    ** rewrite e in H0. auto_contradict.
                    ** entailer.
                ++ split; destruct H; auto.
                    right; unfold Nat.lt; split; try rep_lia; auto.
                ++ forward. destruct (eq_dec pa1 nullval). 
                    ** entailer!. unfold freelistrep; fold freelistrep. entailer!.
                        assert (S n = 0)%nat. { rewrite H8. auto. }
                        try rep_lia.
                    ** entailer!.
                    unfold freelistrep; fold freelistrep.
                    admit. (*there is a lot of junk in memory, I have to take care of*)
Admitted.



Lemma body_client3: semax_body Vprog Gprog f_client3 client3_spec.
Proof.
start_function.
forward_call

forward_call (sh, pa1, original_freelist_pointer, xx, gv, n, PGSIZE, number_structs_available). (* call kfree1 *)
- admit. (* should be easy to prove *)
- forward_call (sh, pa1, xx, (S n), original_freelist_pointer, gv).
    + destruct (eq_dec pa1 nullval) eqn:epa1; try (rewrite S_pred); entailer!.
    + admit. (*EESSY*) (*destruct H as [H1 [H2 [H3 H4]]]; split; auto. right; split; try rep_lia; auto.*)
    + destruct (eq_dec pa1 nullval) eqn:epa1.
        * rewrite e in H0; auto_contradict.
        * forward_call (sh, pa2, original_freelist_pointer, xx, gv, n, PGSIZE, number_structs_available). (* call kfree1 *)
        -- rewrite S_pred; entailer!. admit.
        -- admit.
        -- forward_call (sh, pa2, xx, (S n), original_freelist_pointer, gv).
            ++ destruct (eq_dec pa2 nullval) eqn:epa2.
                entailer!. admit.
            ++ destruct (eq_dec pa2 nullval) eqn:epa2; entailer!.
            ++ admit.
            ++ destruct (eq_dec pa2 nullval) eqn:epa2.
                ** forward. entailer!. admit. admit.
                ** forward. entailer!. admit. admit.
Admitted. *)

Lemma body_client4: semax_body Vprog Gprog f_client4 client4_spec.
Proof.
start_function.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, n, next, number_structs_available).
- EExists. entailer!. admit.
- admit. (* should be easy*)
- 
 forward_call (sh, pa2, original_freelist_pointer, xx, gv, n, next, number_structs_available).
    + entailer!.
    + admit.
    + admit.  (* should be easy*)
    + forward. entailer!. admit. admit.