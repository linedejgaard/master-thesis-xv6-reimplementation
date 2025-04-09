Require Import VST.floyd.proofauto.
Require Import VC.client1.
Require Import VC.helper.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(************************ freelistrep *********************************)
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


Lemma freelistrep_null: forall sh n x,
       x = nullval ->
       freelistrep sh n x = !! (n = nil) && emp.
Proof.
   intros.
   destruct n; unfold freelistrep; fold freelistrep.
   autorewrite with norm. auto.
   apply pred_ext.
   entailer. 
   destruct n; entailer!; try discriminate H0. 
Qed.

Lemma freelistrep_nonnull: forall il sh x,
   x <> nullval ->
   freelistrep sh il x =
   EX head : val, EX tail:list val,
          !! (il = head::tail) && !! malloc_compatible (PGSIZE) x && data_at sh t_run head x * freelistrep sh tail head.
Proof.
   intros; apply pred_ext.
   - destruct il. 
         + unfold freelistrep. entailer!.
         + unfold freelistrep; fold freelistrep. entailer!.
         Exists v il. 
         entailer!. 
   - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. entailer!.
Qed.


(************************ specs *********************************)
Definition kfree1_spec := 
    DECLARE _kfree1
       WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, size:Z, number_structs_available:nat
       PRE [ tptr tvoid]
          PROP(
               writable_share sh /\
               is_pointer_or_null original_freelist_pointer /\
               (Nat.le (S O) (number_structs_available) )  /\ 
               isptr new_head
               ) 
          PARAMS (new_head) GLOBALS(gv)
          SEP (
                available sh (number_structs_available) new_head PGSIZE *
                freelistrep sh ls original_freelist_pointer *
                (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
             )
          )
       POST [ tvoid ]
          PROP(isptr new_head)
          RETURN () 
          SEP (
             !! malloc_compatible (PGSIZE) new_head && 
             data_at sh t_run original_freelist_pointer new_head * 
             freelistrep sh ls original_freelist_pointer *
             available sh (Nat.sub number_structs_available (S O)) (add_offset new_head PGSIZE) PGSIZE *
             data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
             ).

Definition kalloc1_spec :=
DECLARE _kalloc1
WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
PRE [ ]
    PROP(writable_share sh /\ 
        (((ls = nil) /\ original_freelist_pointer = nullval) \/ ((ls <> nil) /\ isptr original_freelist_pointer))
    ) 
    PARAMS () GLOBALS(gv)
    SEP (
        !! malloc_compatible (PGSIZE) original_freelist_pointer && 
        freelistrep sh ls original_freelist_pointer *
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )  
POST [ tptr tvoid ]

    PROP()
    RETURN (original_freelist_pointer) (* we return the head like in the pop function*)
    SEP (
        if (eq_dec original_freelist_pointer nullval) then
        (
            freelistrep sh ls original_freelist_pointer * (* TODO: fix this.. *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* q can be nullval meaning that there is only one run *)
        )
        else 
            (
                EX next ls',
                !! (next :: ls' = ls) &&
                !! malloc_compatible (PGSIZE) original_freelist_pointer && 
                data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                freelistrep sh (tl ls) next *
                data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
            )
        ).


Definition client1_spec := 
DECLARE _client1
WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, ls:list val, next:val, number_structs_available:nat
PRE [ tptr tvoid ]
    PROP(
        writable_share sh /\
        isptr new_head /\
        (Nat.le (S O) number_structs_available) /\
        ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls<> nil /\ isptr original_freelist_pointer))
    ) 
    PARAMS (new_head) GLOBALS(gv)
    SEP (
        (*(EX v,
            !! malloc_compatible (PGSIZE) new_head &&
            data_at sh t_run v new_head) *
        freelistrep sh ls original_freelist_pointer *
        (*available sh number_structs_available new_head PGSIZE **)
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)*)
        available sh (number_structs_available) new_head PGSIZE *
        freelistrep sh ls original_freelist_pointer *
        (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))

    )
POST [ tptr tvoid ]
    PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            data_at sh t_run original_freelist_pointer new_head *
            available sh (number_structs_available - 1) (add_offset new_head PGSIZE) PGSIZE*
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
            ).

Definition client2_spec := 
    DECLARE _client2
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            (*(Nat.le (S (S O)) number_structs_available) /\*)
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (PGSIZE) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (PGSIZE) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            (*available sh number_structs_available pa1 PGSIZE **)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run pa1 pa2 *
                (*available sh (number_structs_available - 1) (add_offset pa2 PGSIZE) PGSIZE **)
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).

Definition client3_spec := 
    DECLARE _client3
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val, number_structs_available:nat
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            (Nat.le (S (S O)) number_structs_available) /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (PGSIZE) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (PGSIZE) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            (*available sh number_structs_available pa1 PGSIZE **)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa2) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run pa1 pa2 *
                (*available sh (number_structs_available - 1) (add_offset pa2 PGSIZE) PGSIZE **)
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), pa1) (gv _kmem)
                ).

Definition client4_spec := 
    DECLARE _client4
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls:list val, next:val, number_structs_available:nat
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            (Nat.le (S (S O)) number_structs_available) /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (PGSIZE) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (PGSIZE) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            (*available sh number_structs_available pa1 PGSIZE **)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa2) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run original_freelist_pointer pa2 *
                (*available sh (number_structs_available - 1) (add_offset pa2 PGSIZE) PGSIZE **)
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).

Definition client5_spec := 
    DECLARE _client5
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls: list val, next:val, number_structs_available:nat
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            (Nat.le (S (S O)) number_structs_available) /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (PGSIZE) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (PGSIZE) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            (*available sh number_structs_available pa1 PGSIZE **)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa2) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run original_freelist_pointer pa2 *
                (*available sh (number_structs_available - 1) (add_offset pa2 PGSIZE) PGSIZE **)
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).

(************** freerange kfree simple ***************)
Definition freerange_while_loop_spec : ident * funspec := (* this is not including admits.. *)
    DECLARE _freerange_while_loop
    WITH b_n_init:block, p_n_init:ptrofs, b_s_init:block, p_s_init:ptrofs, 
            sh : share, original_freelist_pointer : val, xx : Z, gv : globals, ls:list val
    PRE [  tptr tvoid, tptr tvoid ]
        PROP (
                0 <= Ptrofs.unsigned p_s_init <= Ptrofs.unsigned p_n_init /\
                Z.add (Ptrofs.unsigned p_n_init) PGSIZE <= Int.max_signed /\ 
                Z.add (Ptrofs.unsigned p_s_init) PGSIZE <= Int.max_signed /\
                
                writable_share sh /\
                is_pointer_or_null original_freelist_pointer /\
                isptr_lst (Z.to_nat (compute_c (Vptr b_s_init p_s_init) (Vptr b_n_init p_n_init) PGSIZE)) (Vptr b_s_init p_s_init) (PGSIZE) /\
                (*(Nat.le (Z.to_nat (compute_c ((Vptr b_s_init p_s_init) (Vptr b_n_init p_n_init) PGSIZE))) number_structs_available) /\*)
                ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) /\
                b_s_init=b_n_init
                
            
            ) (* the highest number is s + PGSIZE when it fails. The highest s + PGSIZE when it succeeds is n, so the highest after this is n + PGSIZE*)
        PARAMS (Vptr b_s_init p_s_init; Vptr b_n_init p_n_init) GLOBALS (gv)
        SEP (
         ensure_comparable_range sh (add_offset (Vptr b_s_init p_s_init) PGSIZE) (Vptr b_n_init p_n_init) PGSIZE 
         (*denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_init (Ptrofs.repr PGSIZE))) (Vptr b_n_init p_n_init)*) &&
         (((freelistrep sh ls original_freelist_pointer)
            * available_range sh (Vptr b_s_init p_s_init) (Vptr b_n_init p_n_init) PGSIZE
            * (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
               )))
    POST [ tvoid ]
    EX c_final:Z, EX p_s_final:ptrofs, EX curr_head:val, EX final_added_elem : list val,
        PROP (
            Ptrofs.unsigned p_s_final = Z.add (Ptrofs.unsigned p_s_init) (Z.mul c_final PGSIZE) /\ 
            0 <= c_final /\ 
            (Ptrofs.unsigned p_s_final) <= (Ptrofs.unsigned p_n_init) /\ 
            (Ptrofs.unsigned p_n_init) < Z.add (Ptrofs.unsigned p_s_final) PGSIZE /\

            ((curr_head = original_freelist_pointer /\ c_final = 0) \/ (curr_head = (Vptr b_s_init (Ptrofs.sub p_s_final (Ptrofs.repr PGSIZE)))  /\ c_final <> 0)) /\
            final_added_elem = pointers (Z.to_nat c_final) (Vptr b_s_init p_s_init) (PGSIZE)
            )
        RETURN ()
        SEP ((*denote_tc_test_order (Vptr b_s_init (Ptrofs.add p_s_final (Ptrofs.repr PGSIZE))) (Vptr b_n_init p_n_init) &&*)
            if (0<?c_final) then
               (freelistrep sh (final_added_elem ++ ls) (curr_head) *
               available_range sh (Vptr b_s_init p_s_final) (Vptr b_n_init p_n_init) PGSIZE *
               data_at sh t_struct_kmem (Vint (Int.repr xx), (curr_head)) (gv _kmem))
            else
            (((freelistrep sh ls original_freelist_pointer)
            * (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
               ))
        ).

(************************ Gprog  *************************)

Definition Gprog : funspecs := [
    kfree1_spec; 
    kalloc1_spec; 
    client1_spec;
    client2_spec;
    client3_spec;
    client4_spec;
    client5_spec;
    freerange_while_loop_spec
].

(************************ Proofs  *************************)
Lemma body_kfree1: semax_body Vprog Gprog f_kfree1 kfree1_spec.
Proof. start_function. Intros. destruct number_structs_available eqn:en; try rep_lia. destruct H. unfold available. Intros v. repeat forward. 
    entailer. (*fold available.*)
    induction ls. 
    - assert (original_freelist_pointer = nullval). {
         rewrite <- H7; auto.
      }
      unfold freelistrep.
      fold available. rewrite S_pred. entailer!. 
   - fold available. rewrite S_pred. entailer!. 
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
                    freelistrep sh ls original_freelist_pointer * (* TODO: fix this.. *)
                    data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* q can be nullval meaning that there is only one run *)
                )
                else 
                    (
                        EX next ls',
                        !! (next :: ls' = ls) &&
                        data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                        freelistrep sh (tl ls) next *
                        data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
                    )
            )
        )%assert; 
    try (rewrite H012 in H; auto_contradict).
    + destruct ls; auto_contradict. unfold freelistrep; fold freelistrep. Intros. 
    forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. forward. entailer.
    + destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. forward. entailer.
    + rewrite e in H; auto_contradict.
- Intros. destruct H as [H1 [[H111 H112] | [H121 H122]]]; try (subst; auto_contradict).
    destruct ls; auto_contradict; unfold freelistrep; fold freelistrep. Intros. forward.
        forward_if (
            PROP  ( )
            LOCAL (
                temp _r original_freelist_pointer; 
                gvars gv
                )
            SEP (
                if (eq_dec original_freelist_pointer nullval) then
                (
                    freelistrep sh ls original_freelist_pointer * (* TODO: fix this.. *)
                    data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* q can be nullval meaning that there is only one run *)
                )
                else 
                    (
                        EX next ls',
                        !! (next :: ls' = (v::ls)) &&
                        data_at sh t_run next original_freelist_pointer * (* TODO: fix this.. *)
                        freelistrep sh (tl (v::ls)) next *
                        data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
                    )
            )
        )%assert.
        * forward. forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict.
            entailer. Exists v ls. simpl; entailer!.
        * forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict.
        *forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. Intros next ls'. Exists next.
        Exists ls. entailer!.
Qed.

Lemma body_client1: semax_body Vprog Gprog f_client1 client1_spec.
Proof.
start_function.
(*Intros v.*)
forward_call (sh, new_head, original_freelist_pointer, xx, gv, ls, PGSIZE, number_structs_available). (* call kfree1 *)
- destruct H as [HH1 [HH2 [HH3 [[H411 H412] | [H421 H422]]]]]; split; auto; split; auto. rewrite H412; unfold is_pointer_or_null; unfold nullval; simpl; auto.
- forward_call (sh, new_head, xx, original_freelist_pointer::ls, gv). (* call kalloc *)
    + unfold freelistrep; fold freelistrep. entailer!.
    + destruct H as [HH1 [HH2 [HH3 [[H411 H412] | [H421 H422]]]]]; split; auto;  right; split; auto; unfold not; intros; inversion H.
    + destruct (eq_dec new_head nullval) eqn:enh.
        * rewrite e in H0; auto_contradict.
        * forward. simpl; entailer!.
        inversion H4. subst. entailer!.
Qed.

Lemma body_client2: semax_body Vprog Gprog f_client2 client2_spec.
Proof.
start_function.
Intros v1 v2.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls, PGSIZE, S O). (* call kfree1, there is 1 struct available from pa1.. *)
- entailer!. unfold available. 
- destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split; auto; destruct H4; destruct H4; auto. rewrite H5. simpl; auto.
- forward_call (sh, pa2, pa1, xx, gv, (original_freelist_pointer::ls), PGSIZE, (number_structs_available -1)%nat). (* call kfree1 *)
    + Exists v2. entailer. unfold freelistrep; fold freelistrep. entailer!. 
    + destruct H as [HH1 [HH2 [H3 H4]]]; split; auto.
    + forward_call (sh, pa2, xx, (pa1::original_freelist_pointer::ls), pa1, gv). (* call kalloc *)
        * destruct (eq_dec pa2 nullval) eqn:epa2.
            -- entailer!.
            -- simpl. entailer!. 
        * destruct H as [HH1 [HH2 [HH3 H4]]]; split; auto. right. split; auto.
        unfold not; intros; auto_contradict.
        * destruct (eq_dec pa2 nullval) eqn:epa2.
            -- rewrite e in H3; auto_contradict.
            -- forward_call (sh, pa1, xx, (original_freelist_pointer::ls), original_freelist_pointer, gv). (* kalloc *)
                ++ destruct (eq_dec pa1 nullval) eqn:epa1.
                    **repeat (rewrite S_pred). entailer!.
                    **repeat (rewrite S_pred). simpl. entailer!. unfold freelistrep; fold freelistrep. entailer!.
                ++ destruct H as [HH1 [HH2 [HH3 H4]]]; split; auto. right. split; auto. unfold not; intros; auto_contradict.
                ++ destruct (eq_dec pa1 nullval) eqn:epa1.
                    ** forward.
                    ** forward. simpl. entailer!.
Qed.

Lemma body_client3: semax_body Vprog Gprog f_client3 client3_spec.
Proof.
    start_function.
    Intros v1 v2.
    forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls, PGSIZE, number_structs_available). (* call kfree1 *)
    - Exists v1. entailer!.
    - destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split; auto; destruct H4; destruct H4; auto. rewrite H5. simpl; auto.
    - forward_call (sh, pa2, pa1, xx, gv, (original_freelist_pointer::ls), PGSIZE, (number_structs_available -1)%nat). (* call kfree1 *)
        + Exists v2. entailer. unfold freelistrep; fold freelistrep. entailer!. 
        + destruct H as [HH1 [HH2 [H3 H4]]]; split; auto.
        + forward_call (sh, pa2, xx, (pa1::original_freelist_pointer::ls), pa1, gv). (* call kalloc *)
            * destruct (eq_dec pa2 nullval) eqn:epa2.
                -- entailer!.
                -- simpl. entailer!. 
            * destruct H as [HH1 [HH2 [HH3 H4]]]; split; auto. right. split; auto.
            unfold not; intros; auto_contradict.
            * destruct (eq_dec pa2 nullval) eqn:epa2.
                -- rewrite e in H3; auto_contradict.
                -- forward. simpl. unfold freelistrep; fold freelistrep. entailer!.
Qed.

Lemma body_client4: semax_body Vprog Gprog f_client4 client4_spec.
Proof.
start_function.
Intros v1 v2.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls, next, number_structs_available).
- Exists v1. entailer!.
- destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split.
- forward_call (sh, pa2, original_freelist_pointer, xx, gv, ls, next, number_structs_available).
    + Exists v2. entailer!.
    + destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split.
    + (*unfold abbreviate in POSTCONDITION. *) forward. entailer!.
Qed. 

Lemma body_client5: semax_body Vprog Gprog f_client5 client5_spec.
Proof.
start_function.
Intros v1 v2.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls, PGSIZE, number_structs_available). (* call kfree1 *)
- Exists v1. entailer!.
- destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split; auto; destruct H4; destruct H4; auto. rewrite H5. simpl; auto.
- forward_call (sh, pa1, xx, (pa1 :: ls), original_freelist_pointer, gv). (* call kalloc *)
    + destruct (eq_dec pa1 nullval) eqn:epa1.
        * subst; auto_contradict.
        * simpl. entailer!.
    + destruct H as [HH1 [HH2 [H3 H4]]]. destruct H4; split; auto. right; split; auto. unfold not; intros; auto_contradict.
    + destruct (eq_dec pa1 nullval) eqn:epa1.
        * subst; auto_contradict.
        * forward_call (sh, pa2, original_freelist_pointer, xx, gv, ls, PGSIZE, number_structs_available). (* call kfree1 *)
            -- Exists v2. simpl. entailer!.
            --  destruct H as [HH1 [HH2 [H3 H4]]]; split; auto; split; auto. destruct H4. destruct H4.
                ++ destruct H4. rewrite H5. simpl; auto.
                ++ destruct H4; auto.
            -- forward_call (sh, pa2, xx, (pa2::ls), original_freelist_pointer, gv). (* call kalloc *)
                ++ destruct (eq_dec pa2 nullval) eqn:epa2.
                    ** entailer!.
                    ** simpl. entailer!.
                ++ destruct H as [HH1 [HH2 [HH3 H4]]]; split; auto. right. split. unfold not; intros; auto_contradict. auto.
                ++ destruct (eq_dec pa2 nullval) eqn:epa2.
                    ** forward.
                    ** forward. simpl. entailer!.
Qed.

(** loop : it keeps looping from Intros, but I think it is working with admits form another file - probably verif_simple_kfree_file_v2.v ***)

Lemma body_freerange_while_loop_spec: semax_body Vprog Gprog f_freerange_while_loop freerange_while_loop_spec.
Proof. start_function. 
forward_while
 (EX c_tmp:Z, EX p_s_tmp:ptrofs, EX curr_head:val, EX tmp_added_elem : list val,
   PROP  (
    Ptrofs.unsigned p_s_tmp = Z.add (Ptrofs.unsigned p_s_init) (Z.mul c_tmp PGSIZE) /\ 
    0 <= c_tmp /\
    c_tmp <= Int.max_signed /\
    Ptrofs.unsigned p_s_tmp <= Ptrofs.unsigned p_n_init /\
    ((curr_head = original_freelist_pointer /\ c_tmp = 0) \/ (curr_head = (Vptr b_s_init (Ptrofs.sub p_s_tmp (Ptrofs.repr PGSIZE)))  /\ c_tmp <> 0)) /\
    tmp_added_elem = pointers (Z.to_nat c_tmp) (Vptr b_s_init p_s_init) PGSIZE /\
    (c_tmp = (compute_c (Vptr b_s_init p_s_init) (Vptr b_n_init p_s_tmp) PGSIZE))
   )
   LOCAL (
      gvars gv;
      temp _pa_start (Vptr b_s_init p_s_tmp);
      temp _pa_end (Vptr b_n_init p_n_init)
    ) 
   SEP (
      ensure_comparable_range sh (add_offset (Vptr b_s_init p_s_tmp) PGSIZE) (Vptr b_n_init p_n_init) PGSIZE  &&
      (freelistrep sh (tmp_added_elem ++ ls) (curr_head) *
      available_range sh (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) PGSIZE *
      data_at sh t_struct_kmem (Vint (Int.repr xx), curr_head) (gv _kmem))
      )
  )%assert.
   - Exists 0 p_s_init original_freelist_pointer (pointers (Z.to_nat (compute_c (Vptr b_s_init p_s_init) (Vptr b_n_init p_s_init) PGSIZE)) ((Vptr b_s_init p_s_init)) PGSIZE). entailer!. 
   rewrite compute_c_equal.
   2: { unfold PGSIZE; try rep_lia. }
   2: { destruct H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]; subst; auto. }
   split; auto. rewrite compute_c_equal.
   rewrite <- pointers_empty. simpl; entailer!.
   unfold PGSIZE; try rep_lia.
   destruct H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]; subst; auto.
   - entailer. apply andp_left1. unfold ensure_comparable_range. 
     destruct (sameblock (Vptr b_s_init p_s_init) (Vptr b_n_init p_n_init)) eqn:esb; entailer; auto_contradict.
     + assert (Z.to_nat
            (compute_c (add_offset (Vptr b_s_init p_s_tmp) PGSIZE) (Vptr b_n_init p_n_init) PGSIZE +
            1) = S (Z.to_nat
            (compute_c (add_offset (Vptr b_s_init p_s_tmp) PGSIZE) (Vptr b_n_init p_n_init) PGSIZE))). {
            unfold add_offset.
            rewrite Z2Nat.inj_add; try rep_lia.
            unfold compute_c. destruct (PGSIZE <=? 0); try rep_lia.
            unfold Ptrofs.ltu. destruct (zlt (Ptrofs.unsigned p_n_init)
                (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))) eqn:ez; try rep_lia.
            apply Z_div_pos.
            - unfold PGSIZE; try rep_lia.
            - apply Zle_minus_le_0; try rep_lia.
            }
            unfold add_offset.
            destruct (sameblock (Vptr b_s_init (Ptrofs.add p_s_init (Ptrofs.repr PGSIZE)))
            (Vptr b_n_init p_n_init)) eqn:eb.
            * unfold add_offset in H1.
            rewrite H1. unfold ensure_comparable; fold ensure_comparable. destruct c_tmp eqn:ec; try rep_lia.
            -- assert (p_s_tmp = p_s_init). { admit. }
                rewrite H2.
                destruct (sameblock (Vptr b_s_init (Ptrofs.add p_s_init (Ptrofs.repr PGSIZE)))
                (Vptr b_n_init p_n_init)) eqn:eb2; auto_contradict.
                apply andp_left1; unfold PGSIZE; unfold denote_tc_test_order. entailer!.
            -- destruct (sameblock (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))
            (Vptr b_n_init p_n_init)) eqn:eb2; auto_contradict.
                ++ apply andp_left1; unfold PGSIZE; unfold denote_tc_test_order. entailer!.
                ++ assert (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)) = nullval <-> False). {
                    split; intros; auto_contradict.
                }
                rewrite H2. entailer!.
            * destruct (sameblock (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))
            (Vptr b_n_init p_n_init)) eqn:eb2; auto_contradict.
                ++ assert ((Z.to_nat
                (compute_c (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))
                   (Vptr b_n_init p_n_init) PGSIZE + 1)) = 
                S (Z.to_nat
                (compute_c (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))
                    (Vptr b_n_init p_n_init) PGSIZE))). {
                    unfold add_offset.
                    rewrite Z2Nat.inj_add; try rep_lia.
                    unfold compute_c. destruct (PGSIZE <=? 0); try rep_lia.
                    unfold Ptrofs.ltu. destruct (zlt (Ptrofs.unsigned p_n_init)
                        (Ptrofs.unsigned (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)))) eqn:ez; try rep_lia.
                    apply Z_div_pos.
                    - unfold PGSIZE; try rep_lia.
                    - apply Zle_minus_le_0; try rep_lia.
                    }
                    rewrite H2. unfold ensure_comparable; fold ensure_comparable. apply andp_left2.
                    destruct H0 as [H01 [H02 [H03 [H04 [[[H051 H052] | H052] [H061 H062]]]]]].
                    --admit. (* compariable*)
                    -- admit. (* comparison*)
                ++ assert (Vptr b_s_init (Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE)) = nullval <-> False). {
                        split; intros; auto_contradict.
                    }
                    rewrite H2. entailer!.
    + unfold add_offset. apply sameblock_false in esb.  destruct H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]; subst; auto_contradict.
   - forward_call (sh, (Vptr b_s_init p_s_tmp), curr_head, xx, gv, (tmp_added_elem ++ ls), PGSIZE,  (Z.to_nat (compute_c (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) PGSIZE - c_tmp))). (* call kfree1 *)
   (*- forward_call (sh, (Vptr b_s_init p_s_tmp), curr_head, xx, gv, (Nat.add (Z.to_nat c_tmp) n), PGSIZE, (Z.to_nat (compute_c (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) PGSIZE))).*)
      + apply andp_left2. sep_apply available_range_correct. EExists. entailer. destruct c_tmp; try rep_lia.
        * destruct H0 as [H01 [H02 [H03 [H04 [[H051 | H052] H06]]]]].
            -- entailer. rewrite compute_c_equal. rewrite <- available_empty.
                ++ entailer.  inversion H0.
                ++ unfold PGSIZE; rep_lia.
                ++ admit. (* should be provable from HRE *)
            -- admit. (* available*)
        * rewrite compute_c_not_equal with (pt_s := p_s_tmp) (pt_e :=p_n_init) (b :=b_s_init).
            -- entailer. induction (Z.to_nat ((Ptrofs.unsigned p_n_init - Ptrofs.unsigned p_s_tmp) / PGSIZE)).
                ++ assert (Vptr b_s_init p_s_tmp = nullval). { rewrite <- H7. auto. }
                    inversion H9.
                ++ unfold available; fold available. Intros v. entailer!. admit. (* available..*)
            -- unfold PGSIZE; rep_lia.
            -- admit. (* b_s_init and b_n_init should be equal to be able to compare. *)
            -- apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.
                admit. (* should be provable from HRE*) 
            -- auto.
            --  admit. (* b_s_init and b_n_init should be equal to be able to compare. should be provable form HRE *)
      + admit. (* look at assumptions*)
      + admit. (*Intros. forward. Exists (c_tmp + 1, Ptrofs.add p_s_tmp (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tschar)) (ptrofs_of_int Signed (Int.repr PGSIZE))), Vptr b_s_init p_s_tmp). (* Vptr b_s_init p_s_tmp is current head*)
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
          ++ apply sameblock_false in eb. apply typed_true_same_block in HRE; auto_contradict.*)
 - forward. Exists c_tmp p_s_tmp curr_head tmp_added_elem. entailer!. (* the loop invariant (and negation of the loop condition) is a strong enough precondition to prove the MORE-COMMANDS after the loop *)
          ++ split_lia. 
             apply typed_false_offset_val_leq with (b_s_init:=b_s_init) (b_n_init:=b_n_init); try rep_lia; unfold PGSIZE; try rep_lia; auto.
             destruct H0 as [H01 [H02 [H03 [H04 [[[H051 H052] | H052] [H061 H062]]]]]]; split; auto.
          ++ apply andp_left2. destruct (0 <? c_tmp) eqn:ec.
          --- destruct H0 as [H01 [H02 [H03 [H04 H05]]]].
                destruct H05; destruct H0. destruct H0.
                +++ rewrite H2 in ec. auto_contradict.
                +++ subst. entailer. (*DER ER STADIG PROBLEMER MED HOVEDET...*)
          --- destruct H0 as [H01 [H02 [H03 [H04 H05]]]];  assert (0 = c_tmp); try rep_lia.
             destruct H05.
             +++ destruct H1. 2: { rewrite H0 in H1; try rep_lia. } 
             rewrite <- H0 in H2. destruct H2.
             rewrite<- pointers_empty in H2. rewrite H2. simpl; entailer!. destruct H1; subst. entailer.
             assert (p_s_tmp = p_s_init). { admit. (* should be provable*) }
             admit. (* should be ok as there is no available.. else available is wrongly defined.. *)
Admitted.