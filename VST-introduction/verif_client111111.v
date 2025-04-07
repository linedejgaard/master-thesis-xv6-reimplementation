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
        !! malloc_compatible (sizeof t_run) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        data_at sh t_run next p * (* at the location p, there is a t_run structure with the value next *)
        freelistrep sh il' next (* "*" ensures no loops... *)
 | nil => !! (p = nullval) && emp
 end.

Arguments freelistrep sh il p : simpl never.

Ltac refold_freelistrep :=
  unfold freelistrep;
  fold freelistrep.

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
   destruct n; refold_freelistrep.
   autorewrite with norm. auto.
   apply pred_ext.
   entailer. 
   destruct n; entailer!; try discriminate H0. 
Qed.

Lemma freelistrep_nonnull: forall il sh x,
   x <> nullval ->
   freelistrep sh il x =
   EX head : val, EX tail:list val,
          !! (il = head::tail) && !! malloc_compatible (sizeof t_run) x && data_at sh t_run head x * freelistrep sh tail head.
Proof.
   intros; apply pred_ext.
   - destruct il. 
         + unfold freelistrep. entailer!.
         + refold_freelistrep. entailer!.
         Exists v il. 
         entailer!. 
   - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. entailer!.
Qed.



(************************ specs *********************************)
Definition kfree1_spec := 
    DECLARE _kfree1
       WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, size:Z
       PRE [ tptr tvoid]
          PROP(
               writable_share sh /\
               is_pointer_or_null original_freelist_pointer /\
               isptr new_head
               ) 
          PARAMS (new_head) GLOBALS(gv)
          SEP (
                (EX v,
                !! malloc_compatible (sizeof t_run) new_head &&
                data_at sh t_run v new_head) * freelistrep sh ls original_freelist_pointer *
                (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
             )
          )
       POST [ tvoid ]
          PROP(isptr new_head)
          RETURN () 
          SEP (
             !! malloc_compatible (sizeof t_run) new_head && 
             data_at sh t_run original_freelist_pointer new_head * 
             freelistrep sh ls original_freelist_pointer *
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
        if (eq_dec original_freelist_pointer nullval) then
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        else 
            (!! malloc_compatible (sizeof t_run) original_freelist_pointer && 
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
        )  
POST [ tptr tvoid ]
    PROP()
    RETURN (original_freelist_pointer) (* we return the head like in the pop function*)
    SEP (
        if (eq_dec original_freelist_pointer nullval) then
        (
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* q can be nullval meaning that there is only one run *)
        )
        else 
            (
                EX next ls',
                (!! (next :: ls' = ls) &&
                !! malloc_compatible (sizeof t_run) original_freelist_pointer && 
                data_at sh t_run next original_freelist_pointer *
                freelistrep sh ls' next *
                data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem))
            )
        ).


Definition client1_spec := 
DECLARE _client1
WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, ls:list val
PRE [ tptr tvoid ]
    PROP(
        writable_share sh /\
        isptr new_head /\
        ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls<> nil /\ isptr original_freelist_pointer))
    ) 
    PARAMS (new_head) GLOBALS(gv)
    SEP (
        (EX v,
            !! malloc_compatible (sizeof t_run) new_head &&
            data_at sh t_run v new_head) *
        freelistrep sh ls original_freelist_pointer *
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
    )
POST [ tptr tvoid ]
    PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            data_at sh t_run original_freelist_pointer new_head *
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
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (sizeof t_run) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (sizeof t_run) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run pa1 pa2 *
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).

Definition client3_spec := 
    DECLARE _client3
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (sizeof t_run) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (sizeof t_run) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa2) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run pa1 pa2 *
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), pa1) (gv _kmem)
                ).

Definition client4_spec := 
    DECLARE _client4
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls:list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (sizeof t_run) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (sizeof t_run) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa2) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run original_freelist_pointer pa2 *
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).

Definition client5_spec := 
    DECLARE _client5
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls: list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr pa1 /\
            isptr pa2 /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            (EX v1,
                !! malloc_compatible (sizeof t_run) pa1 &&
                data_at sh t_run v1 pa1) *
            (EX v2,
                !! malloc_compatible (sizeof t_run) pa2 &&
                data_at sh t_run v2 pa2) *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa2) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run original_freelist_pointer pa1 *
                data_at sh t_run original_freelist_pointer pa2 *
                freelistrep sh ls original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
                ).


Definition client6_spec := 
    DECLARE _client6
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            writable_share sh /\
            isptr_lst (2)%nat pa1 PGSIZE /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) /\
            Int.min_signed <= Int.signed (Int.repr 2) + Int.signed (Int.repr 1) <= Int.max_signed
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            available sh (2)%nat pa1 PGSIZE *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (add_offset pa1 PGSIZE) (* we return the head like in the pop function*)
            SEP 
            (
                data_at sh t_run pa1 (add_offset pa1 PGSIZE) *
                freelistrep sh (original_freelist_pointer::ls) pa1 *
                data_at sh t_struct_kmem (Vint (Int.repr xx), pa1) (gv _kmem)
                ).
Print hd.

Definition client7_spec := 
    DECLARE _client7
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            writable_share sh /\
            isptr_lst (Z.to_nat n)%nat pa1 PGSIZE /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            available sh (Z.to_nat n) pa1 PGSIZE *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        EX before_head, EX before_alloc_fl, (* TODO: fix top and next is the same?? *)
        PROP( 
            before_alloc_fl = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE original_freelist_pointer)++ls /\
            before_head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE original_freelist_pointer)++ls))
            (*top = hd nullval before_alloc_fl = next *)
            (* final_fl = tl before_alloc_fl *)
            (*top = (hd (nullval) (pointers_with_original_head (Z.to_nat (n)) pa1 PGSIZE original_freelist_pointer)) /\
            next = (hd (nullval) (pointers_with_original_head (Z.to_nat (n-1)) pa1 PGSIZE original_freelist_pointer))*)
        )
            RETURN (hd nullval before_alloc_fl) (* we return the head like in the pop function*)
            SEP 
            (
                if eq_dec before_head nullval then
                    (freelistrep sh (tl before_alloc_fl) (hd nullval before_alloc_fl) *
                    data_at sh t_struct_kmem (Vint (Int.repr xx), hd nullval before_alloc_fl) (gv _kmem))
                else
                    (data_at sh t_run (hd nullval before_alloc_fl) (before_head) *
                    freelistrep sh (tl before_alloc_fl) (hd nullval before_alloc_fl) *
                    data_at sh t_struct_kmem (Vint (Int.repr xx), hd nullval before_alloc_fl) (gv _kmem))
                ).

Definition client8_spec := 
    DECLARE _client8
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            writable_share sh /\
            isptr_lst (Z.to_nat n)%nat pa1 PGSIZE /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            available sh (Z.to_nat n) pa1 PGSIZE *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tvoid ]
        EX head, EX added_elem, (* TODO: fix top and next is the same?? *)
        PROP( 
            added_elem = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE original_freelist_pointer) /\
            head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE original_freelist_pointer)++ls))
            )
            RETURN () (* we return the head like in the pop function*)
            SEP 
            (
                freelistrep sh (added_elem++ls) head *
                data_at sh t_struct_kmem (Vint (Int.repr xx), head) (gv _kmem)
                ).

Definition client9_spec := 
    DECLARE _client9
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            writable_share sh /\
            isptr_lst (Z.to_nat n)%nat pa1 PGSIZE /\
            ((ls = nil /\ original_freelist_pointer = nullval) \/ (ls <> nil /\ isptr original_freelist_pointer)) /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            available sh (Z.to_nat n) pa1 PGSIZE *
            freelistrep sh ls original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        )
    POST [ tptr tvoid ]
        EX head, EX added_elem, (* TODO: fix top and next is the same?? *)
        PROP( 
            added_elem = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE original_freelist_pointer) /\
            head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE original_freelist_pointer)++ls))
            )
            RETURN () (* we return the head like in the pop function*)
            SEP 
            (
                freelistrep sh (added_elem++ls) head *
                data_at sh t_struct_kmem (Vint (Int.repr xx), head) (gv _kmem)
                ).
(* added values: 
(pointers_with_original_head (Z.to_nat (n-1)) (pa1) PGSIZE original_freelist_pointer)
*)

(************** freerange kfree simple ***************)
(*Definition freerange_while_loop_spec : ident * funspec := (* this is not including admits.. *)
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
        ).*)

(************************ Gprog  *************************)

Definition Gprog : funspecs := [
    kfree1_spec; 
    kalloc1_spec; 
    client1_spec;
    client2_spec;
    client3_spec;
    client4_spec;
    client5_spec;
    client6_spec;
    client7_spec;
    client8_spec(*;
    freerange_while_loop_spec*)
].

(************************ Proofs  *************************)
Lemma body_kfree1: semax_body Vprog Gprog f_kfree1 kfree1_spec.
Proof. start_function. Intros. (*destruct number_structs_available eqn:en; try rep_lia. destruct H.*) 
Intros v. forward. destruct H as [H [H1 H2]]. repeat forward. 
    entailer. 
    induction ls. 
    - assert (original_freelist_pointer = nullval). {
         rewrite <- H5; auto.
      }
      (*rewrite H11.*) unfold freelistrep.
      (*rewrite S_pred.*)
      entailer.
   - (*rewrite S_pred.*) entailer!. 
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
    + destruct ls; auto_contradict. refold_freelistrep. Intros. 
    forward. destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. entailer. refold_freelistrep. entailer!.
    +forward.
    + destruct (eq_dec original_freelist_pointer nullval) eqn:e1; auto_contradict. destruct ls; auto_contradict. refold_freelistrep. Intros. forward. forward. entailer.
    + forward. entailer.
    + forward.
- Intros. destruct H as [H1 [[H111 H112] | [H121 H122]]]; try (subst; auto_contradict).
    destruct ls; auto_contradict; refold_freelistrep. Intros. forward.
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
        Exists ls. simpl. entailer!.
Qed.

Lemma body_client1: semax_body Vprog Gprog f_client1 client1_spec.
Proof.
start_function.
(*Intros v.*)
forward_call (sh, new_head, original_freelist_pointer, xx, gv, ls, PGSIZE). (* call kfree1 *)
- destruct H as [HH1 [HH2 [[H411 H412] | [H421 H422]]]]; split; auto; split; auto. rewrite H412; unfold is_pointer_or_null; unfold nullval; simpl; auto.
- forward_call (sh, new_head, xx, original_freelist_pointer::ls, gv). (* call kalloc *)
    + refold_freelistrep. destruct (eq_dec new_head nullval); try (rewrite e in H0; auto_contradict). entailer!. 
    + destruct H as [HH1 [HH2 [[H411 H412] | [H421 H422]]]]; split; auto;  right; split; auto; unfold not; intros; inversion H.
    + destruct (eq_dec new_head nullval) eqn:enh.
        * rewrite e in H0; auto_contradict.
        * forward. simpl; entailer!.
        inversion H1. subst. entailer!.
Qed.

Lemma body_client2: semax_body Vprog Gprog f_client2 client2_spec.
Proof.
start_function.
Intros v1 v2.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls, PGSIZE). (* call kfree1 *)
- Exists v1. entailer!.
- destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split; auto; destruct H; auto; subst; simpl; auto.
- forward_call (sh, pa2, pa1, xx, gv, (original_freelist_pointer::ls), PGSIZE). (* call kfree1 *)
    + Exists v2. entailer. refold_freelistrep. entailer!. 
    + destruct H as [HH1 [HH2 [H3 H4]]]; split; auto.
    + forward_call (sh, pa2, xx, (pa1::original_freelist_pointer::ls), gv). (* call kalloc *)
        * destruct (eq_dec pa2 nullval) eqn:epa2.
            -- entailer!.
            -- refold_freelistrep. entailer!.  
        * destruct H as [HH1 [HH2 [HH3 H4]]]; split; auto. right. split; auto.
        unfold not; intros; auto_contradict.
        * destruct (eq_dec pa2 nullval) eqn:epa2.
            -- rewrite e in H3; auto_contradict.
            -- Intros ab. inversion H4. forward_call (sh, pa1, xx, (original_freelist_pointer::ls), gv). (* kalloc *)
                ++ destruct (eq_dec pa1 nullval) eqn:epa1.
                    ** rewrite e in H2; inversion H2.
                    ** simpl. refold_freelistrep. rewrite H7. refold_freelistrep. entailer!.
                ++ destruct H as [HH1 [HH2 [HH3 HH4]]]; split; auto. right. split; auto. unfold not; intros; auto_contradict.
                ++ destruct (eq_dec pa1 nullval) eqn:epa1.
                    ** rewrite e in H2; inversion H2.
                    ** forward. simpl. inversion H6. rewrite H11. entailer!.
Qed.

Lemma body_client3: semax_body Vprog Gprog f_client3 client3_spec.
Proof.
    start_function.
    Intros v1 v2.
    forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls, PGSIZE). (* call kfree1 *)
    - Exists v1. entailer!.
    - destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split; auto; destruct H; auto; subst; simpl; auto.
    - forward_call (sh, pa2, pa1, xx, gv, (original_freelist_pointer::ls), PGSIZE). (* call kfree1 *)
        + Exists v2. entailer. refold_freelistrep. entailer!. 
        + destruct H as [HH1 [HH2 [H3 H4]]]; split; auto.
        + forward_call (sh, pa2, xx, (pa1::original_freelist_pointer::ls), gv). (* call kalloc *)
            * destruct (eq_dec pa2 nullval) eqn:epa2.
                -- entailer!.
                -- refold_freelistrep. entailer!.  
            * destruct H as [HH1 [HH2 [HH3 H4]]]; split; auto. right. split; auto.
            unfold not; intros; auto_contradict.
            * destruct (eq_dec pa2 nullval) eqn:epa2.
                -- rewrite e in H3; auto_contradict.
                -- Intros ab. inversion H4. forward.
                simpl. refold_freelistrep. rewrite H7. refold_freelistrep. entailer!.
Qed.

Lemma body_client4: semax_body Vprog Gprog f_client4 client4_spec.
Proof.
start_function.
Intros v1 v2.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls).
- Exists v1. entailer!.
- destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split.
- forward_call (sh, pa2, original_freelist_pointer, xx, gv, ls).
    + Exists v2. entailer!.
    + destruct H as [HH1 [H2 [H3 H4]]]. destruct H4; split; auto; split.
    + (*unfold abb iate in POSTCONDITION. *) forward. entailer!.
Qed. 

Lemma body_client5: semax_body Vprog Gprog f_client5 client5_spec.
Proof.
start_function.
Intros v1 v2.
forward_call (sh, pa1, original_freelist_pointer, xx, gv, ls, PGSIZE). (* call kfree1 *)
-  Exists v1. entailer!.
- destruct H as [HH1 [HH2 [H3 [[H411 H412] | [H421 H422]]]]]; split; auto; split; auto. rewrite H412; unfold is_pointer_or_null; unfold nullval; simpl; auto.
- forward_call (sh, pa1, xx, original_freelist_pointer::ls, gv). (* call kalloc *)
    + refold_freelistrep. destruct (eq_dec pa1 nullval); try (rewrite e in H0; auto_contradict). entailer!. 
    + destruct H as [HH1 [HH2 [H3 [[H411 H412] | [H421 H422]]]]]; split; auto;  right; split; auto; unfold not; intros; inversion H.
    + destruct (eq_dec pa1 nullval) eqn:enh.
        * rewrite e in H0; auto_contradict.
        * Intros ab. inversion H3. rewrite H5; rewrite H6.
          forward_call (sh, pa2, original_freelist_pointer, xx, gv, ls, PGSIZE).  (* call kfree1 *)
          -- Exists v2. entailer!.
          -- destruct H as [HH1 [HH2 [HH3 [[H411 H412] | [H421 H422]]]]]; split; auto; split; auto. rewrite H412; unfold is_pointer_or_null; unfold nullval; simpl; auto.
          -- forward_call (sh, pa2, xx, original_freelist_pointer::ls, gv). (* call kalloc *)
            ++ refold_freelistrep. destruct (eq_dec pa2 nullval); try (rewrite e in H0; auto_contradict). entailer!. entailer!.  
            ++split; destruct H; auto. right; split; auto; unfold not; intros; auto_contradict.
            ++ destruct (eq_dec pa2 nullval) eqn:enh2.
                ** forward.
                ** Intros ab0. forward. inversion H7. rewrite H6; rewrite H17. entailer!.
Qed.

Lemma body_client6: semax_body Vprog Gprog f_client6 client6_spec.
Proof.
    start_function.
    Intros. forward. (*forward. unfold abb iate in POSTCONDITION.*)
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= 2 /\
        ((curr_head = original_freelist_pointer /\ i = 0) \/ (curr_head = (sub_offset p_tmp PGSIZE)  /\ i <> 0)) /\
        tmp_added_elem = (pointers_with_original_head (Z.to_nat i) (pa1) PGSIZE original_freelist_pointer) /\
        p_tmp = add_offset pa1 (i * PGSIZE)%Z /\
        Int.min_signed <=
        Int.signed (Int.repr i) + Int.signed (Int.repr 1) <=
        Int.max_signed 
    )
    LOCAL (
        gvars gv;
        temp _pa_start p_tmp;
        temp _i (Vint (Int.repr i))
        ) 
    SEP (
        (freelistrep sh (tmp_added_elem ++ ls) (curr_head) *
        available sh (Z.to_nat(2-i)) p_tmp PGSIZE *
        data_at sh t_struct_kmem (Vint (Int.repr xx), curr_head) (gv _kmem))
        )
    )%assert.
    - entailer. Exists 0 pa1 original_freelist_pointer (pointers_with_original_head (Z.to_nat 0) pa1 PGSIZE original_freelist_pointer). (*entailer. *)
        rewrite <- pointers_with_head_empty. simpl; entailer. Exists v. entailer.
        Exists x. entailer!. unfold add_offset. destruct pa1; auto_contradict.
    - entailer.
    - Intros. destruct (Z.to_nat (2 - i)) eqn:e1; refold_available.
        +assert (i = 2); try rep_lia.
        +forward_call (sh, p_tmp, curr_head, xx, gv, (tmp_added_elem ++ ls), PGSIZE). (* call kfree1 *)
            * Intros v. Exists v. entailer!.
            * destruct H as [H1 [H2 [[[H311 H312] | [H321 H322]] H4]]]; destruct H0 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]]; split; auto; split; try (subst; simpl; auto);  unfold isptr_lst in H2; destruct H2; try (rewrite add_offset_0; auto);
                  try (unfold add_offset; unfold sub_offset; unfold_size (i * PGSIZE)%Z e0; destruct i; auto_contradict;
                  destruct pa1; auto_contradict;
                  unfold sub_offset; unfold is_pointer_or_null; auto; simpl; auto); repeat (destruct H01; try rep_lia).
            *Intros. forward. forward. Exists ((((i+1)%Z, (add_offset p_tmp PGSIZE):val), p_tmp:val), (curr_head::(pointers_with_original_head(Z.to_nat (i)) pa1 PGSIZE)original_freelist_pointer):list val).
                entailer!.
                destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H0 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]]; 
                repeat split; try rep_lia; auto; auto_contradict; try (subst; simpl; try rep_lia); try ( unfold isptr_lst in HH2; destruct HH2; auto);
                try (rewrite add_offset_0; auto); try (apply add_offset_eq_offset_val); auto.
                ++ right; split; try rep_lia. rewrite sub_add_offset_correct; auto.
                ++ right; split; try rep_lia. rewrite sub_add_offset_correct; auto; apply PGSIZE_gt_0.
                ++ replace (Z.to_nat (i + 1)) with (S (Z.to_nat (i))); try rep_lia. unfold pointers_with_original_head at 2; fold pointers_with_original_head.
                destruct (Z.to_nat i) eqn:ei.
                    ** assert (i = 0); try rep_lia.
                    ** unfold pointers_acc; fold pointers_acc. simpl. induction n0; assert (i = 1); try rep_lia.
                    simpl. rewrite H13; rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0.
                ++ rewrite add_offset_add; auto; try apply PGSIZE_gt_0; rep_lia.
                ++ try rep_lia.
                ++ right. rewrite sub_add_offset_correct; auto. split; auto; unfold not; intros; auto_contradict.
                ++ assert (i = 1); try rep_lia. right; rewrite H13. unfold not; intros; split; try rep_lia.
                    rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0. rewrite Z.mul_1_l; destruct H0; auto.
                ++ replace (Z.to_nat (i + 1)) with (S (Z.to_nat (i))); try rep_lia.  assert (i = 1); try rep_lia. rewrite H13; rewrite Z.mul_1_l. simpl. rewrite sub_add_offset_correct; auto; apply PGSIZE_gt_0.
                ++assert (i = 1); try rep_lia. rewrite H13. rewrite add_offset_add; auto; try apply PGSIZE_gt_0; try rep_lia.
                ++ try rep_lia.
                ++ destruct H0 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
                    ** rewrite H031.  rewrite H0212. unfold pointers_with_original_head. destruct (Z.to_nat 0) eqn:e0; try rep_lia.
                    simpl. refold_freelistrep. assert (n = S O); try rep_lia. rewrite H0. unfold available. entailer.
                    **assert (i = 1); try rep_lia. rewrite H031.  rewrite H0. simpl. refold_freelistrep. assert (n = O); try rep_lia. rewrite H13. unfold available. entailer!.
    - forward_call (sh, add_offset pa1 PGSIZE, xx, (pa1::original_freelist_pointer::ls), gv). (* call kalloc *)
    + entailer. 
      destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H0 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]]; rewrite H031; refold_freelistrep; entailer.
        * unfold pointers_with_original_head. assert (i = 2); try rep_lia. rewrite H7. destruct (0 <? Z.to_nat 2)%nat eqn:ei; try rep_lia.
            -- assert (sub_offset (add_offset pa1 (2 * PGSIZE)) PGSIZE = (add_offset pa1 (1 * PGSIZE))). {
            rewrite sub_add_offset_n with (p := pa1) (size := PGSIZE) (n :=2); try rep_lia; auto.
            apply PGSIZE_gt_0.
            unfold isptr_lst in HH2; destruct HH2; auto.
            }
            rewrite H8. simpl. refold_freelistrep.  destruct (EqDec_val (add_offset pa1 PGSIZE) nullval); try (rewrite e in H0; auto_contradict). entailer!. entailer!.  
            --  assert (0 < Z.to_nat 2)%nat; try rep_lia. auto_contradict.
        * assert (i = 2); try rep_lia. rewrite H7. replace (Z.to_nat 2) with (S (S O)); try rep_lia.
            unfold pointers_with_original_head; fold pointers_with_original_head.
            assert (sub_offset (add_offset pa1 (2 * PGSIZE)) PGSIZE = (add_offset pa1 (1 * PGSIZE))). {
            rewrite sub_add_offset_n with (p := pa1) (size := PGSIZE) (n :=2); try rep_lia; auto.
            apply PGSIZE_gt_0.
            unfold isptr_lst in HH2; destruct HH2; auto.
            } rewrite H8. unfold pointers_acc. simpl. refold_freelistrep. destruct (EqDec_val (add_offset pa1 PGSIZE) nullval); try (rewrite e in H0; auto_contradict). entailer!. entailer!.
    + destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; split; auto.
        * right; split; auto; unfold not; intros. inversion H. unfold isptr_lst in HH2; destruct HH2 as [HH21 [HH22 HH23]]; auto.
        * right. split; auto. unfold not. intros. inversion H. unfold isptr_lst in HH2; destruct HH2 as [HH21 [HH22 HH23]]; auto.
    + forward. 
        * destruct (eq_dec (add_offset pa1 PGSIZE) nullval) eqn:ee; auto_contradict.
            destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; unfold isptr_lst in HH2; destruct HH2 as [HH21 [HH22 HH23]]; rewrite e in HH22; auto_contradict.
            Intros ab. inversion H2. entailer!.
Qed. 

Lemma body_client7: semax_body Vprog Gprog f_client7 client7_spec.
Proof.
start_function.
        assert (isptr pa1). {
                destruct H as [H1 [HH2 HH3]].
                destruct (Z.to_nat n) eqn:en; unfold isptr_lst in HH2; fold isptr_lst in HH2; auto.
                destruct HH2; auto.
            }
    Intros. forward. (*forward. unfold abb iate in POSTCONDITION.*)
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= n /\
        ((curr_head = original_freelist_pointer /\ i = 0) \/ (curr_head = (sub_offset p_tmp PGSIZE)  /\ i <> 0)) /\
        tmp_added_elem = (pointers_with_original_head (Z.to_nat i) (pa1) PGSIZE original_freelist_pointer) /\
        p_tmp = add_offset pa1 (i * PGSIZE)%Z /\
        Int.min_signed <=
        Int.signed (Int.repr i) + Int.signed (Int.repr 1) <=
        Int.max_signed 
    )
    LOCAL (
        gvars gv;
        temp _pa_start p_tmp;
        temp _i (Vint (Int.repr i));
        temp _n (Vint (Int.repr n))
        ) 
    SEP (
        (freelistrep sh (tmp_added_elem ++ ls) (curr_head) *
        available sh (Z.to_nat(n-i)) p_tmp PGSIZE *
        data_at sh t_struct_kmem (Vint (Int.repr xx), curr_head) (gv _kmem))
        )
    )%assert.
    - entailer. Exists 0 pa1 original_freelist_pointer (pointers_with_original_head (Z.to_nat 0) pa1 PGSIZE original_freelist_pointer). (*entailer. *)
        rewrite <- pointers_with_head_empty. entailer. destruct (Z.to_nat n).
            + unfold available. entailer!.
            + refold_available. Intros v. Exists v. simpl. entailer!. rewrite add_offset_0; auto.
    - entailer.
    - Intros. destruct (Z.to_nat (n - i)) eqn:e1; refold_available.
        + try rep_lia.
        +forward_call (sh, p_tmp, curr_head, xx, gv, (tmp_added_elem ++ ls), PGSIZE). (* call kfree1 *)
            * Intros v. Exists v. entailer!.
            * destruct H as [HH1 [H2 [[[H311 H312] | [H321 H322]] H4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]]; split; auto; split; try (subst; simpl; auto).
                ++ destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia. rewrite add_offset_0; auto;
                unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2; auto.
                ++ rewrite sub_add_offset_n. unfold add_offset. destruct pa1; try (unfold nullval; simpl; auto). unfold_size ((i - 1) * PGSIZE)%Z e2; try simpl; auto. apply PGSIZE_gt_0.
                destruct i eqn:ei; auto_contradict; try rep_lia. destruct (Z.to_nat n) eqn:en; try rep_lia.
                unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2; auto.
                ++ destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia. unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2.
                   unfold add_offset; destruct pa1; auto_contradict. auto. unfold_size ((i) * PGSIZE)%Z e2; try simpl; auto. assert (0 > i * PGSIZE); try rep_lia. rewrite Z.leb_gt in e2. admit.
                ++ rewrite add_offset_0; auto;destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2;
                unfold add_offset; destruct pa1; auto_contradict; auto.
                ++ rewrite sub_add_offset_n. unfold add_offset. destruct pa1; auto_contradict; try (unfold nullval; simpl; auto).
                    ** unfold_size ((i - 1) * PGSIZE)%Z e2; try simpl; auto.
                    **  apply PGSIZE_gt_0.
                    ** try rep_lia.
                    ** destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2;
                    unfold add_offset; destruct pa1; auto_contradict; auto.
                ++ unfold add_offset. destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2;
                unfold add_offset; destruct pa1; auto_contradict; auto.
                unfold_size (i * PGSIZE)%Z e2; auto. admit.
            * Intros. forward. forward. Exists ((((i+1)%Z, (add_offset p_tmp PGSIZE):val), p_tmp:val), ((pointers_with_original_head(Z.to_nat (i+1)) pa1 PGSIZE)original_freelist_pointer):list val).
                entailer!.
                destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
                ++ repeat split; try rep_lia; auto; auto_contradict; try (subst; simpl; try rep_lia); try ( unfold isptr_lst in HH2; destruct HH2; auto);
                try (rewrite add_offset_0; auto); try (apply add_offset_eq_offset_val); auto; try rep_lia.
                right; split; try rep_lia. rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0.
                ++ repeat split; try rep_lia; auto; auto_contradict; try (subst; simpl; try rep_lia); try ( unfold isptr_lst in HH2; destruct HH2; auto);
                try (rewrite add_offset_0; auto); try (apply add_offset_eq_offset_val); auto.
                    **right; split; try rep_lia. rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0.
                    **replace (Z.to_nat (i + 1)) with (S (Z.to_nat (i))); try rep_lia. apply add_offset_add; auto; try rep_lia; apply PGSIZE_gt_0. 
                    ** destruct HH4. destruct H.
                    assert (n + 1 <= Int.max_signed); try rep_lia.
                    rewrite Int.signed_repr in H14; try rep_lia. rewrite Int.signed_repr in H14; try rep_lia.
                    ** try rep_lia.
                ++ split; try rep_lia. split. split. 
                    ** right. split; try rep_lia. rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0.
                    ** split. 
                        --- rewrite H0321. 
                        apply add_offset_add; auto; try rep_lia; apply PGSIZE_gt_0. 
                        --- split; try rep_lia; rewrite H0212; try rep_lia.
                    ** unfold PGSIZE; apply add_offset_eq_offset_val; try rep_lia. rewrite H0321.
                    rewrite H0212. simpl. rewrite add_offset_0;
                    destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in HH2; fold isptr_lst in HH2; destruct HH2;
                    unfold add_offset; destruct pa1; auto_contradict; auto.
                ++ split; try rep_lia. split. 
                    **split.
                        --- right. split; try rep_lia. rewrite sub_add_offset_correct; auto; apply PGSIZE_gt_0.
                        --- split.
                            +++ rewrite H0321. apply add_offset_add; auto; try rep_lia; apply PGSIZE_gt_0. 
                            +++ split; try rep_lia.
                                destruct HH4. destruct H. rewrite Int.signed_repr in H14; try rep_lia. rewrite Int.signed_repr in H14; try rep_lia.
                    ** apply add_offset_eq_offset_val; try rep_lia. rewrite H0321.
                        unfold add_offset. destruct pa1 eqn:ep; auto_contradict. unfold_size (i * PGSIZE)%Z e; auto. admit.
                ++ destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
                    ** rewrite H031. rewrite H0212. simpl. refold_freelistrep. entailer.
                        simpl. entailer!. assert (n0 = Z.to_nat (n - 1)); try rep_lia.
                        rewrite H18. entailer.
                    ** entailer. rewrite sub_add_offset_n; try rep_lia.
                        --- simpl. refold_freelistrep. entailer!.
                        assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia.
                        rewrite H16. entailer!. destruct (Z.to_nat (i + 1)) eqn:ei; try rep_lia.
                        destruct ((pointers_with_original_head (S n0) pa1 PGSIZE nullval ++
                            [])) eqn:elst.
                            +++ rewrite app_nil_r in elst. 
                            assert (pointers_with_original_head (S n0) pa1 PGSIZE nullval <> []). { 
                            apply pointers_with_head_non_empty.
                            auto. rep_lia.
                            }
                            auto_contradict.
                            +++ refold_freelistrep. entailer. rewrite app_nil_r in *. 
                            destruct (pointers_with_original_head (S n0) pa1 PGSIZE nullval) eqn:en;  auto_contradict.
                            unfold pointers_with_original_head in en. destruct n0 eqn:en0.
                                *** assert (i=0); try rep_lia.
                                *** inversion en. inversion elst. 
                                assert (Z.of_nat n1 = (i-1)); try rep_lia. rewrite elst in en. 
                                assert ((add_offset pa1 ((i-1) * PGSIZE))::(pointers_with_original_head (Z.to_nat i) pa1 PGSIZE nullval) = pointers_acc (S n1) pa1 PGSIZE [nullval]). {
                                    replace (Z.to_nat i) with (S n1); try rep_lia.
                                    replace (i-1) with (Z.of_nat (n1)); try rep_lia.
                                    unfold pointers_with_original_head. destruct n1 eqn:en1.
                                    ---- unfold pointers_acc. simpl. rewrite add_offset_0; auto. 
                                    ---- rewrite add_to_pointers_with_head; auto.
                                }
                                rewrite <- H20 in en.
                                inversion en. 
                                entailer!.
                        --- apply PGSIZE_gt_0.
                        --- auto.
                    **  assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia. rewrite H.
                        rewrite H031. 
                        rewrite H0212. simpl. refold_freelistrep. entailer.
                    **  assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia. rewrite H.
                        rewrite H031.
                        assert ((curr_head)::(pointers_with_original_head (Z.to_nat i) pa1 PGSIZE
                            original_freelist_pointer ++ ls) = pointers_with_original_head (Z.to_nat (i + 1)) pa1 PGSIZE
                            original_freelist_pointer ++ ls). {
                            destruct (Z.to_nat i) eqn:ei; try rep_lia.
                            replace (Z.to_nat (i + 1)) with (S (S n1)); try rep_lia.
                            unfold pointers_with_original_head. destruct (n1) eqn:esn1.
                            ---- unfold pointers_acc. simpl. rewrite H0221. rewrite H0321. rewrite sub_add_offset_n; auto; try rep_lia. 
                                unfold add_offset. destruct pa1; auto_contradict. 
                                assert (i - 1 = 0); try rep_lia.
                                rewrite H1. simpl.
                                replace (Ptrofs.repr 0) with Ptrofs.zero; auto. rewrite Ptrofs.add_zero. auto.
                                apply PGSIZE_gt_0.
                            ---- rewrite H0221. rewrite H0321. rewrite sub_add_offset_n; auto; try rep_lia.
                            assert (Z.of_nat (S n2) = (i-1)); try rep_lia.
                            rewrite <- H1.
                            rewrite app_comm_cons. rewrite add_to_pointers_with_head; auto.
                            apply PGSIZE_gt_0. 
                            }
                            rewrite <- H1. refold_freelistrep. entailer.
- forward_call (sh, curr_head, xx, (tmp_added_elem++ls), gv). (* call kalloc *)
    + entailer. destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]]; rewrite H031; refold_freelistrep; entailer.
        * simpl. rewrite add_offset_0.
            -- assert (n = 0); try rep_lia. 
            assert (add_offset pa1 (0 * PGSIZE) = nullval). { rewrite <- H4; try rep_lia. }
            simpl in H9.
            rewrite add_offset_0 in H9; auto.
            rewrite H9 in H0; auto_contradict.
            -- destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in HH2; fold isptr_lst in HH2. auto.
        * destruct (Z.to_nat (n - i)) eqn:en; try rep_lia. refold_available.
            entailer. rewrite sub_add_offset_n; try rep_lia.
            -- assert (isptr (add_offset pa1 (i * PGSIZE))). {
                    unfold add_offset. destruct pa1; auto_contradict.
                    unfold_size (i * PGSIZE)%Z e1; auto. admit.
                }
                assert (0 > 0)%nat. { rewrite H5. auto. }
                try rep_lia.
            -- apply PGSIZE_gt_0.
            -- destruct (Z.to_nat n) eqn:en1; auto_contradict; try rep_lia; unfold isptr_lst in HH2; fold isptr_lst in HH2; destruct HH2; auto.
        * entailer. simpl. destruct ls; auto_contradict. refold_freelistrep.  destruct (EqDec_val original_freelist_pointer nullval); try (rewrite e in H0; auto_contradict). entailer!. entailer!.
        * assert (Z.to_nat (n - i) = 0%nat); try rep_lia. rewrite H8. refold_available.
        assert (add_offset pa1 (i * PGSIZE) = nullval). { rewrite <- H4; auto. }
        unfold add_offset in H9. 
        unfold_size (i * PGSIZE)%Z e. destruct pa1 eqn:epa1; auto_contradict. admit.
    + destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; split; auto; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
            * left. subst; split; auto.
            * right. split.
                -- destruct ((Z.to_nat i)) eqn:ei; try rep_lia. unfold not; intro.
                destruct tmp_added_elem; auto_contradict.
                unfold pointers_with_original_head in H031. destruct n0. discriminate H031. (*discriminate H031.*)
                assert (pointers_with_original_head (S (S n0)) pa1 PGSIZE original_freelist_pointer <> []). {
                    apply pointers_with_head_non_empty; auto; try rep_lia.
                }
                unfold pointers_with_original_head in H1. rewrite <- H031 in H1. auto_contradict.
                -- rewrite H0221. rewrite H0321. rewrite sub_add_offset_n.
                unfold_size (i * PGSIZE)%Z e.
                ++ unfold add_offset. unfold_size ((i-1) * PGSIZE)%Z e1.
                destruct pa1; auto_contradict. auto.
                admit.
                ++ admit.
                ++ apply PGSIZE_gt_0.
                ++ try rep_lia.
                ++ destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in HH2; fold isptr_lst in HH2; destruct HH2;
                    unfold add_offset; destruct pa1; auto_contradict; auto.
            * right. split.
                -- subst. unfold not in H321. unfold not. simpl. apply H321.
                -- subst; auto.
            * right. split.
                -- rewrite H031. unfold not; intros.
                    apply app_eq_nil in H. destruct H. auto_contradict.
                -- rewrite H0221. rewrite H0321.
                rewrite sub_add_offset_n; try rep_lia; auto.
                unfold add_offset. destruct pa1; auto_contradict. unfold_size ((i - 1) * PGSIZE)%Z e1. auto. admit.
                apply PGSIZE_gt_0.
    + forward. destruct (eq_dec curr_head nullval) eqn:ee; auto_contradict.
        *destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
            -- assert (n = 0); try rep_lia. rewrite H. Exists original_freelist_pointer (tmp_added_elem++ls). destruct (eq_dec original_freelist_pointer nullval); auto_contradict.
            simpl. entailer.
            -- assert (isptr (sub_offset p_tmp PGSIZE)). {
                rewrite H0321. rewrite sub_add_offset_n; auto; try rep_lia.
                unfold add_offset; destruct pa1; auto_contradict; auto.  unfold_size ((i - 1) * PGSIZE)%Z e1. auto. admit.
                apply PGSIZE_gt_0.
            }
            rewrite <- H0221 in H; rewrite e in H; auto_contradict.
            -- subst. inversion H322.
            -- rewrite H031. Exists curr_head (tmp_added_elem ++ls). assert (i = n); try rep_lia. rewrite H. 
                assert (isptr (sub_offset p_tmp PGSIZE)). {
                    rewrite H0321. rewrite sub_add_offset_n; auto; try rep_lia.
                    unfold add_offset.  unfold_size ((i - 1) * PGSIZE)%Z e1. destruct pa1; auto_contradict. auto. admit. destruct pa1; auto_contradict. auto. apply PGSIZE_gt_0.
                }
            rewrite e in H0221. rewrite <- H0221 in H1. auto_contradict.
        * Intros ab. destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
            -- subst. auto_contradict.
            -- Exists curr_head (tmp_added_elem ++ls). destruct (eq_dec curr_head nullval) eqn:ech; auto_contradict.
                rewrite H031. assert (i = n); try rep_lia. rewrite H. entailer. repeat (rewrite app_nil_r).
                rewrite app_nil_r in *.
                assert (tl (pointers_with_original_head (Z.to_nat n) pa1 PGSIZE nullval) = snd ab). { inversion H4. simpl; auto. }
                assert ((hd nullval (pointers_with_original_head (Z.to_nat n) pa1 PGSIZE nullval)) = fst ab). {inversion H4. simpl; auto. }
                rewrite H16. rewrite H. entailer!.
                ++ admit.
                ++ admit.
            -- Exists curr_head (tmp_added_elem ++ls). destruct (eq_dec curr_head nullval) eqn:ech; auto_contradict.
               entailer. simpl. assert (n = 0); try rep_lia. rewrite H12. simpl. entailer.
               destruct ls; auto_contradict. simpl in H4. simpl. unfold add_offset in H13. destruct pa1; auto_contradict; auto.
            -- Exists curr_head (tmp_added_elem ++ls). destruct (eq_dec curr_head nullval) eqn:ech; auto_contradict. subst. simpl in H4. assert (n = i); try rep_lia. rewrite H. 
            entailer.
            assert (hd nullval (pointers_with_original_head (Z.to_nat i) pa1 PGSIZE
                original_freelist_pointer ++ ls) = fst ab). { inversion H5. simpl; auto. }
            assert (tl (pointers_with_original_head (Z.to_nat i) pa1 PGSIZE
                original_freelist_pointer ++ ls) = snd ab). { inversion H5. simpl; auto. }
                rewrite H. rewrite H15. entailer!. 
                ++split.
                    ** (*apply hd_add_offset_ls; try rep_lia. auto. *) rewrite sub_add_offset_n; auto; try rep_lia. admit.
                        apply PGSIZE_gt_0.
                    ** rewrite sub_add_offset_n; try rep_lia; auto. 2: {apply PGSIZE_gt_0. } admit.
                ++ admit.
Admitted.            


Lemma body_client8: semax_body Vprog Gprog f_client8 client8_spec.
Proof.
start_function.
        assert (isptr pa1). {
                destruct H as [H1 [HH2 HH3]].
                destruct (Z.to_nat n) eqn:en; unfold isptr_lst in HH2; fold isptr_lst in HH2; auto.
                destruct HH2; auto.
            }
    Intros. forward. (*forward. unfold abb iate in POSTCONDITION.*)
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= n /\
        ((curr_head = original_freelist_pointer /\ i = 0) \/ (curr_head = (sub_offset p_tmp PGSIZE)  /\ i <> 0)) /\
        tmp_added_elem = (pointers_with_original_head (Z.to_nat i) (pa1) PGSIZE original_freelist_pointer) /\
        p_tmp = add_offset pa1 (i * PGSIZE)%Z /\
        Int.min_signed <=
        Int.signed (Int.repr i) + Int.signed (Int.repr 1) <=
        Int.max_signed 
    )
    LOCAL (
        gvars gv;
        temp _pa_start p_tmp;
        temp _i (Vint (Int.repr i));
        temp _n (Vint (Int.repr n))
        ) 
    SEP (
        (freelistrep sh (tmp_added_elem ++ ls) (curr_head) *
        available sh (Z.to_nat(n-i)) p_tmp PGSIZE *
        data_at sh t_struct_kmem (Vint (Int.repr xx), curr_head) (gv _kmem))
        )
    )%assert.
    - entailer. Exists 0 pa1 original_freelist_pointer (pointers_with_original_head (Z.to_nat 0) pa1 PGSIZE original_freelist_pointer). (*entailer. *)
        rewrite <- pointers_with_head_empty. entailer. destruct (Z.to_nat n).
            + unfold available. entailer!.
            + refold_available. Intros v. Exists v. simpl. entailer!. rewrite add_offset_0; auto.
    - entailer.
    - Intros. destruct (Z.to_nat (n - i)) eqn:e1; refold_available.
        + try rep_lia.
        +forward_call (sh, p_tmp, curr_head, xx, gv, (tmp_added_elem ++ ls), PGSIZE). (* call kfree1 *)
            * Intros v. Exists v. entailer!.
            * destruct H as [HH1 [H2 [[[H311 H312] | [H321 H322]] H4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]]; split; auto; split; try (subst; simpl; auto).
                ++ destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia. rewrite add_offset_0; auto;
                unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2; auto.
                ++ rewrite sub_add_offset_n. unfold add_offset. destruct pa1; try (unfold nullval; simpl; auto). unfold_size ((i - 1) * PGSIZE)%Z e2; try simpl; auto. apply PGSIZE_gt_0.
                destruct i eqn:ei; auto_contradict; try rep_lia. destruct (Z.to_nat n) eqn:en; try rep_lia.
                unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2; auto.
                ++ destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia. unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2.
                   unfold add_offset; destruct pa1; auto_contradict. auto. unfold_size ((i) * PGSIZE)%Z e2; try simpl; auto. 
                    assert (0 < i * PGSIZE). { apply positive_product; try rep_lia. apply PGSIZE_gt_0. } try rep_lia.
                ++ rewrite add_offset_0; auto;destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2;
                unfold add_offset; destruct pa1; auto_contradict; auto.
                ++ rewrite sub_add_offset_n. unfold add_offset. destruct pa1; auto_contradict; try (unfold nullval; simpl; auto).
                    ** unfold_size ((i - 1) * PGSIZE)%Z e2; try simpl; auto.
                    **  apply PGSIZE_gt_0.
                    ** try rep_lia.
                    ** destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2;
                    unfold add_offset; destruct pa1; auto_contradict; auto.
                ++ unfold add_offset. destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in H2; fold isptr_lst in H2; destruct H2;
                unfold add_offset; destruct pa1; auto_contradict; auto.
                unfold_size (i * PGSIZE)%Z e2; auto. 
                assert (0 < i * PGSIZE). { apply positive_product; try rep_lia. apply PGSIZE_gt_0. } try rep_lia.
            * Intros. forward. forward. Exists ((((i+1)%Z, (add_offset p_tmp PGSIZE):val), p_tmp:val), ((pointers_with_original_head(Z.to_nat (i+1)) pa1 PGSIZE)original_freelist_pointer):list val).
                entailer!.
                destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
                ++ repeat split; try rep_lia; auto; auto_contradict; try (subst; simpl; try rep_lia); try ( unfold isptr_lst in HH2; destruct HH2; auto);
                try (rewrite add_offset_0; auto); try (apply add_offset_eq_offset_val); auto; try rep_lia.
                right; split; try rep_lia. rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0.
                ++ repeat split; try rep_lia; auto; auto_contradict; try (subst; simpl; try rep_lia); try ( unfold isptr_lst in HH2; destruct HH2; auto);
                try (rewrite add_offset_0; auto); try (apply add_offset_eq_offset_val); auto.
                    **right; split; try rep_lia. rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0.
                    **replace (Z.to_nat (i + 1)) with (S (Z.to_nat (i))); try rep_lia. apply add_offset_add; auto; try rep_lia; apply PGSIZE_gt_0. 
                    ** destruct HH4. destruct H.
                    assert (n + 1 <= Int.max_signed); try rep_lia.
                    rewrite Int.signed_repr in H14; try rep_lia. rewrite Int.signed_repr in H14; try rep_lia.
                    ** try rep_lia.
                ++ split; try rep_lia. split. split. 
                    ** right. split; try rep_lia. rewrite sub_add_offset_correct; auto. apply PGSIZE_gt_0.
                    ** split. 
                        --- rewrite H0321. 
                        apply add_offset_add; auto; try rep_lia; apply PGSIZE_gt_0. 
                        --- split; try rep_lia; rewrite H0212; try rep_lia.
                    ** unfold PGSIZE; apply add_offset_eq_offset_val; try rep_lia. rewrite H0321.
                    rewrite H0212. simpl. rewrite add_offset_0;
                    destruct (Z.to_nat n) eqn:en; auto_contradict; try rep_lia; unfold isptr_lst in HH2; fold isptr_lst in HH2; destruct HH2;
                    unfold add_offset; destruct pa1; auto_contradict; auto.
                ++ split; try rep_lia. split. 
                    **split.
                        --- right. split; try rep_lia. rewrite sub_add_offset_correct; auto; apply PGSIZE_gt_0.
                        --- split.
                            +++ rewrite H0321. apply add_offset_add; auto; try rep_lia; apply PGSIZE_gt_0. 
                            +++ split; try rep_lia.
                                destruct HH4. destruct H. rewrite Int.signed_repr in H14; try rep_lia. rewrite Int.signed_repr in H14; try rep_lia.
                    ** apply add_offset_eq_offset_val; try rep_lia. rewrite H0321.
                        unfold add_offset. destruct pa1 eqn:ep; auto_contradict. unfold_size (i * PGSIZE)%Z e; auto. 
                        assert (0 < i * PGSIZE). { apply positive_product; try rep_lia. apply PGSIZE_gt_0. } try rep_lia.
                ++ destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]].
                    ** rewrite H031. rewrite H0212. simpl. refold_freelistrep. entailer.
                        simpl. entailer!. assert (n0 = Z.to_nat (n - 1)); try rep_lia.
                        rewrite H18. entailer.
                    ** entailer. rewrite sub_add_offset_n; try rep_lia.
                        --- simpl. refold_freelistrep. entailer!.
                        assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia.
                        rewrite H16. entailer!. destruct (Z.to_nat (i + 1)) eqn:ei; try rep_lia.
                        destruct ((pointers_with_original_head (S n0) pa1 PGSIZE nullval ++
                            [])) eqn:elst.
                            +++ rewrite app_nil_r in elst. 
                            assert (pointers_with_original_head (S n0) pa1 PGSIZE nullval <> []). { 
                            apply pointers_with_head_non_empty.
                            auto. rep_lia.
                            }
                            auto_contradict.
                            +++ refold_freelistrep. entailer. rewrite app_nil_r in *. 
                            destruct (pointers_with_original_head (S n0) pa1 PGSIZE nullval) eqn:en;  auto_contradict.
                            unfold pointers_with_original_head in en. destruct n0 eqn:en0.
                                *** assert (i=0); try rep_lia.
                                *** inversion en. inversion elst. 
                                assert (Z.of_nat n1 = (i-1)); try rep_lia. rewrite elst in en. 
                                assert ((add_offset pa1 ((i-1) * PGSIZE))::(pointers_with_original_head (Z.to_nat i) pa1 PGSIZE nullval) = pointers_acc (S n1) pa1 PGSIZE [nullval]). {
                                    replace (Z.to_nat i) with (S n1); try rep_lia.
                                    replace (i-1) with (Z.of_nat (n1)); try rep_lia.
                                    unfold pointers_with_original_head. destruct n1 eqn:en1.
                                    ---- unfold pointers_acc. simpl. rewrite add_offset_0; auto. 
                                    ---- rewrite add_to_pointers_with_head; auto.
                                }
                                rewrite <- H20 in en.
                                inversion en. 
                                entailer!.
                        --- apply PGSIZE_gt_0.
                        --- auto.
                    **  assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia. rewrite H.
                        rewrite H031. 
                        rewrite H0212. simpl. refold_freelistrep. entailer.
                    **  assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia. rewrite H.
                        rewrite H031.
                        assert ((curr_head)::(pointers_with_original_head (Z.to_nat i) pa1 PGSIZE
                            original_freelist_pointer ++ ls) = pointers_with_original_head (Z.to_nat (i + 1)) pa1 PGSIZE
                            original_freelist_pointer ++ ls). {
                            destruct (Z.to_nat i) eqn:ei; try rep_lia.
                            replace (Z.to_nat (i + 1)) with (S (S n1)); try rep_lia.
                            unfold pointers_with_original_head. destruct (n1) eqn:esn1.
                            ---- unfold pointers_acc. simpl. rewrite H0221. rewrite H0321. rewrite sub_add_offset_n; auto; try rep_lia. 
                                unfold add_offset. destruct pa1; auto_contradict. 
                                assert (i - 1 = 0); try rep_lia.
                                rewrite H1. simpl.
                                replace (Ptrofs.repr 0) with Ptrofs.zero; auto. rewrite Ptrofs.add_zero. auto.
                                apply PGSIZE_gt_0.
                            ---- rewrite H0221. rewrite H0321. rewrite sub_add_offset_n; auto; try rep_lia.
                            assert (Z.of_nat (S n2) = (i-1)); try rep_lia.
                            rewrite <- H1.
                            rewrite app_comm_cons. rewrite add_to_pointers_with_head; auto.
                            apply PGSIZE_gt_0. 
                            }
                            rewrite <- H1. refold_freelistrep. entailer.
- forward. Exists curr_head tmp_added_elem. entailer.
  destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; destruct H1 as [H01 [[[H0211 H0212] | [H0221 H0222]] [H031 [H0321 H0322]]]]; rewrite H031; refold_freelistrep; entailer.
  + simpl. rewrite add_offset_0; auto. refold_freelistrep. entailer. assert (n = 0); try rep_lia.  rewrite H10; unfold pointers_with_original_head. simpl. entailer.
  + repeat (rewrite app_nil_r). destruct (Z.to_nat (n - i)) eqn:en; try rep_lia. refold_available.
        entailer. rewrite sub_add_offset_n; try rep_lia.
        -- assert (isptr (add_offset pa1 (i * PGSIZE))). {
                unfold add_offset. destruct pa1; auto_contradict.
                unfold_size (i * PGSIZE)%Z e1; auto. 
                assert (0 < i * PGSIZE). { apply positive_product; try rep_lia. apply PGSIZE_gt_0. } try rep_lia.
            }
            assert (0 > 0)%nat. { rewrite H5. auto. }
            try rep_lia.
        -- apply PGSIZE_gt_0.
        -- destruct (Z.to_nat n) eqn:en1; auto_contradict; try rep_lia; unfold isptr_lst in HH2; fold isptr_lst in HH2; destruct HH2; auto.
 + entailer. simpl. destruct ls; auto_contradict. refold_freelistrep. entailer. assert (n = 0); try rep_lia. rewrite H18. simpl. entailer.
 + destruct ((Z.to_nat (n - i))) eqn:e1; try rep_lia. simpl.
    entailer. assert (isptr (add_offset pa1 (i * PGSIZE))). { 
        unfold add_offset. unfold_size (i * PGSIZE)%Z e; destruct pa1; auto_contradict; auto. assert (0 < i * PGSIZE). { apply positive_product; try rep_lia. apply PGSIZE_gt_0. } try rep_lia.
    }
    rewrite H8 in H9; auto_contradict.
Qed.

Lemma body_client9: semax_body Vprog Gprog f_client9 client9_spec.
Proof.
start_function.
assert (isptr pa1). {
                destruct H as [H1 [HH2 HH3]].
                destruct (Z.to_nat n) eqn:en; unfold isptr_lst in HH2; fold isptr_lst in HH2; auto.
                destruct HH2; auto.
            }
forward_call (sh, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z).
- destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; split; auto.
- Intros vret. forward_call (sh, fst vret, xx, snd vret ++ ls, gv). (* call kalloc *)
    + destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]. 
        * destruct (eq_dec (fst vret) nullval).
            -- entailer!.
            -- destruct (snd vret).
                ++ entailer. simpl. entailer!. assert (fst vret = nullval). { rewrite <- H7. auto. }
                auto_contradict.
                ++ simpl. refold_freelistrep. entailer.
        * destruct (eq_dec (fst vret) nullval).
            -- entailer!.
            -- destruct (snd vret).
                ++ destruct (Z.to_nat n); auto_contradict.
                2: { 
                    assert (pointers_with_original_head (S n1) pa1 PGSIZE original_freelist_pointer <> []). { apply pointers_with_head_non_empty; auto; try rep_lia. }
                    rewrite H1 in H. auto_contradict.
                }
                rewrite app_nil_l. destruct ls; auto_contradict.
                refold_freelistrep. entailer!.
                ++ simpl. refold_freelistrep. entailer.
    + destruct H as [HH1 [HH2 [[[H311 H312] | [H321 H322]] HH4]]]; split; auto.
        * destruct (Z.to_nat n).
            -- simpl in H1. left; subst. split; auto. unfold pointers_with_original_head in H1. rewrite H1. auto.
            -- right. split; auto. rewrite H311. rewrite app_nil_r. rewrite H1.
                apply pointers_with_head_non_empty; auto; try rep_lia. admit.
        * right. split. destruct (snd vret).
            -- rewrite app_nil_l. auto.
            -- unfold not. intros; auto_contradict.
            -- admit.
    + forward. destruct (eq_dec (fst vret) nullval).
        * Exists (fst vret). Exists (nil:list val). destruct (eq_dec nullval nullval).
            -- destruct (eq_dec (fst vret) nullval); auto_contradict. admit.
            -- unfold not in n0. exfalso; apply n0; auto.
        * admit.
Admitted.




            
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
   2: { apply PGSIZE_gt_0. }
   2: { destruct H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]; subst; auto. }
   split; auto. rewrite compute_c_equal.
   rewrite <- pointers_empty. simpl; entailer!.
   apply PGSIZE_gt_0.
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
            - apply PGSIZE_gt_0.
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
                    - apply PGSIZE_gt_0.
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
   - forward_call (sh, (Vptr b_s_init p_s_tmp), curr_head, xx, gv, (tmp_added_elem ++ ls), PGSIZE). (* call kfree1 *)
   (*- forward_call (sh, (Vptr b_s_init p_s_tmp), curr_head, xx, gv, (Nat.add (Z.to_nat c_tmp) n), PGSIZE, (Z.to_nat (compute_c (Vptr b_s_init p_s_tmp) (Vptr b_n_init p_n_init) PGSIZE))).*)
      + apply andp_left2. sep_apply available_range_correct. EExists. entailer. destruct c_tmp; try rep_lia.
        * destruct H0 as [H01 [H02 [H03 [H04 [[H051 | H052] H06]]]]].
            -- entailer. rewrite compute_c_equal. rewrite <- available_empty.
                ++ entailer.  inversion H0.
                ++ apply PGSIZE_gt_0.
                ++ admit. (* should be provable from HRE *)
            -- admit. (* available*)
        * rewrite compute_c_not_equal with (pt_s := p_s_tmp) (pt_e :=p_n_init) (b :=b_s_init).
            -- entailer. induction (Z.to_nat ((Ptrofs.unsigned p_n_init - Ptrofs.unsigned p_s_tmp) / PGSIZE)).
                ++ assert (Vptr b_s_init p_s_tmp = nullval). { rewrite <- H7. auto. }
                    inversion H9.
                ++ unfold available; fold available. Intros v. entailer!. admit. (* available..*)
            -- apply PGSIZE_gt_0.
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
          apply PGSIZE_gt_0.
       -- apply c_tmp_bounds_max with (p_s_init:=p_s_init) (p_s_tmp:=p_s_tmp) (p_n_init:=p_n_init); try rep_lia.
       -- rewrite ptrofs_add_simpl; try rep_lia.
          ++ apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.
             rewrite ptrofs_add_simpl in HRE; try rep_lia.   
             ** simplify_signed_PGSIZE. 
             ** (* this is the almost the same as above.. *)  split; try rep_lia.
             apply Z.le_lt_trans with (m := Int.max_signed); try rep_lia.
             (*apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.*)
             apply Z.le_trans with (m := Ptrofs.unsigned p_n_init + PGSIZE); try rep_lia.
             apply PGSIZE_gt_0.
          ++ split; try rep_lia. simplify_signed_PGSIZE.
          ++ (** this is the same as above*)simplify_signed_PGSIZE; split_lia. apply Z.le_lt_trans with (m := Int.max_signed); try rep_lia.
             (*apply typed_true_offset_val_leq with (b_s_init:=b_s_init) (b_n_init :=b_n_init) in HRE; unfold PGSIZE; auto.*)
             apply Z.le_trans with (m := Ptrofs.unsigned p_n_init + PGSIZE); try rep_lia.
             apply PGSIZE_gt_0.
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
                      rewrite <- ptrofs_add_simpl; auto; apply PGSIZE_gt_0.
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
             apply typed_false_offset_val_leq with (b_s_init:=b_s_init) (b_n_init:=b_n_init); try rep_lia; apply PGSIZE_gt_0; auto.
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