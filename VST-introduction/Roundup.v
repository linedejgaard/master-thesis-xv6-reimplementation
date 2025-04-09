(** rounds up...*)
Definition PGSIZE : nat := 4096. (** I think we should be able to retrieve this.. but it has to be greater than 0 *)

(* PGROUNDUP function in Coq *)
Definition PGROUNDUP (sz : nat) : nat :=
  ((sz + PGSIZE - 1) / PGSIZE) * PGSIZE.

(* Lemma 1: PGROUNDUP always returns a multiple of PGSIZE *)
Lemma PGROUNDUP_multiple_of_PGSIZE : forall sz,
exists n : nat, PGROUNDUP sz = Nat.mul n PGSIZE.
Proof.
intro sz.
unfold PGROUNDUP; destruct sz.
- exists O. unfold PGSIZE; auto.
- exists ((S sz + PGSIZE - 1) / PGSIZE)%nat; auto.
Qed.

(*Lemma helper1 : forall b:nat,
   (O <= b)%nat -> 
   (b / S b)%nat = O.
Proof.
   intros; auto. apply Nat.div_small. rep_lia.
Qed.*)

(* Lemma 2: PGROUNDUP rounds sz up to the next multiple of PGSIZE *)
Lemma PGROUNDUP_le: forall sz:nat,
  (sz <= (PGROUNDUP sz))%nat.
Proof.
intros.
induction sz; auto.
inversion IHsz.
- rewrite <- H.
  unfold PGROUNDUP. 
  assert (((S sz + PGSIZE - 1) / PGSIZE)%nat = ((sz + PGSIZE) / PGSIZE)%nat). {
   simpl. rewrite Nat.sub_0_r; auto.
  }
  rewrite H0.
  assert (((sz + PGSIZE) / PGSIZE)%nat = ((sz / PGSIZE) + (PGSIZE / PGSIZE))%nat). {
  assert ((1* PGSIZE)%nat = PGSIZE). { try rep_lia. }
  rewrite <- H1 at 1.
  rewrite Nat.div_add; auto. unfold PGSIZE. auto.
  }
  rewrite H1. assert ((PGSIZE / PGSIZE)%nat = S O); auto.
  rewrite H2.
  assert (((sz / PGSIZE + 1) * PGSIZE)%nat = (((sz*PGSIZE / PGSIZE) + (1*PGSIZE)))%nat). {
  rewrite Nat.mul_add_distr_r.
  replace (1 * PGSIZE)%nat with (PGSIZE)%nat by lia.
  assert ((sz / PGSIZE * PGSIZE)%nat = (sz * PGSIZE / PGSIZE)%nat). {
    remember (sz / PGSIZE)%nat as q.
    remember (sz mod PGSIZE)%nat as r.
    assert (sz = (q * PGSIZE + r)%nat). {admit.
    }
Admitted.

(* Lemma 3: PGROUNDUP returns sz if sz is already a multiple of PGSIZE *)
Lemma PGROUNDUP_equals_sz_when_aligned : forall sz : nat,
  (sz mod PGSIZE)%nat = O -> PGROUNDUP sz = sz.
Proof.
Admitted.



// skraldespand for free range..


Definition PGSIZE : Z := 4096.

Definition freerange_no_loop_no_add_spec := 
 DECLARE _freerange_no_loop_no_add
   WITH sh : share, pa_start:val, pa_end:val, original_freelist_pointer:val, xx:Z, gv:globals
   PRE [ tptr tvoid, tptr tvoid]
      PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) (* writable_share is necessary *)
      PARAMS (pa_start; pa_end) GLOBALS(gv)
      SEP (data_at sh (t_run) nullval pa_start; (* the input run struct should exists *)
      data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* the kmem freelist should exists, xx is a placeholder for the spinlock *)
      )
   POST [ tvoid ]
      PROP()
      RETURN () (* no return value *)
      SEP (
         if (denote_tc_test_order pa_start pa_end) then
         (data_at sh (t_run) (original_freelist_pointer) pa_start * (* the new head should point to the original freelist pointer *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), pa_start) (gv _kmem)) (** the top of the freelist should point to the new head *)
         else 
         data_at sh (t_run) nullval pa_start * (* the input run struct should exists *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
   ).

Definition if_condition_bool (pa_start pa_end : val) : bool :=
  match pa_start, pa_end with
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if eq_dec b1 b2 then
        Z.leb (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr PGSIZE))) (Ptrofs.unsigned ofs2)
      else
        false
  | _, _ => false
  end.

Lemma if_condition_bool_example :
  forall (b : block) (ofs1 ofs2 : ptrofs),
  Z.leb (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr PGSIZE))) (Ptrofs.unsigned ofs2) = true ->
  if_condition_bool (Vptr b ofs1) (Vptr b ofs2) = true.
Proof.
  intros b ofs1 ofs2 H.
  unfold if_condition_bool.
  destruct (eq_dec b b); auto.
Qed.

Lemma if_condition_bool_different_block :
  forall (b1 b2 : block) (ofs1 ofs2 : ptrofs),
  b1 <> b2 ->
  if_condition_bool (Vptr b1 ofs1) (Vptr b2 ofs2) = false.
Proof.
intros b1 b2 ofs1 ofs2 H.
  unfold if_condition_bool.
  destruct (eq_dec b1 b2); auto.
  rewrite e in H; try contradiction.
Qed.

Definition freerange_no_loop_spec := 
 DECLARE _freerange_no_loop
   WITH sh : share, pa_start:val, pa_end:val, original_freelist_pointer:val, xx:Z, gv:globals
   PRE [ tptr tvoid, tptr tvoid]
      PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) (* writable_share is necessary *)
      PARAMS (pa_start; pa_end) GLOBALS(gv)
      SEP (data_at sh (t_run) nullval pa_start; (* the input run struct should exists *)
      data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* the kmem freelist should exists, xx is a placeholder for the spinlock *)
      )
   POST [ tvoid ]
      PROP()
      RETURN () (* no return value *)
      SEP (
         if (if_condition_bool pa_start pa_end) then
         (data_at sh (t_run) (original_freelist_pointer) pa_start * (* the new head should point to the original freelist pointer *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), pa_start) (gv _kmem)) (** the top of the freelist should point to the new head *)
         else 
         data_at sh (t_run) nullval pa_start * (* the input run struct should exists *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
   ).


(*Definition freerange_no_loop_spec :=
  DECLARE _freerange_no_loop
    WITH pa_start: val, pa_end: val, sh: share, original_freelist_pointer:val, xx:Z,gv:globals
    PRE [ tptr tvoid, tptr tvoid ]
      PROP (writable_share sh; is_pointer_or_null pa_start; is_pointer_or_null pa_end) (*;
      (exists start end_, start <= end_ -> (pa_start = Vptr start) /\ (pa_end = Vptr end_))*)
      PARAMS (pa_start; pa_end)
      SEP (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)) (* Memory permissions should be specified *)
    POST [ tvoid ]
    EX new_head,
      PROP () RETURN ()
      SEP (
         if 
         data_at sh (t_run) next original_freelist_pointer;
         data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
      ). (* Update to specify that all pages in the range are freed *)*)






      forward_while
      (EX i: Z,
        PROP  (0 <= i <= n)
        LOCAL (temp _s (Vint (Int.repr i)); temp _n (Vint (Int.repr n)))
        SEP   ()).
        - EExists; entailer.
        - entailer.
        - forward; entailer!. EExists. inversion HRE. entailer!. rep_lia.
        - forward. entailer!. split.
         + destruct H0. destruct H1; try discriminate; try contradiction; try rep_lia.
         Search (_ >= _). destruct H1; try rep_lia. Search ()
       +_
         unfold Lt in H2. unfold Int.lt in H1. destruct (zlt (Int.signed (Int.repr i)) (Int.signed n)); try discriminate; try contradiction.
           assert (Int.signed (Int.repr i) = i) by (apply Int.signed_repr; try rep_lia). 
           rewrite H0 in l. assert (i + 1 <= Int.signed n) by lia. try rep_lia. 
         + EExists. entailer!.  inversion HRE. unfold Int.lt in H1. destruct (zlt (Int.signed (Int.repr i)) (Int.signed n)); try discriminate; try contradiction.
             assert (Int.signed (Int.repr i) = i) by (apply Int.signed_repr; try rep_lia). 
             rewrite H0 in l. assert (i + 1 <= Int.signed n) by lia. try rep_lia. 
       - forward. entailer!. inversion HRE. unfold 
     
     
        + entailer
        2: {
        EExists. entailer!.  }
        +entailer!.
     
     
     
     
     
     
     
     
     
     
     
     (*Lemma body_loop_2: semax_body Vprog Gprog f_loop_2 loop_2_spec.
     Proof. start_function. forward.
     forward_while
      (EX i: Z,
        PROP (0 <= i <= Int.max_signed)
        LOCAL (temp _n (Vint (Int.repr i)); temp _pa_start (Vptr b_s p_s);
               temp _pa_end (Vptr b_e p_e))
        SEP (denote_tc_test_order (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE)))
        (Vptr b_e p_e))); try entailer. 
        - EExists. entailer!; try rep_lia. (* the precondition (of the whole loop) implies the loop invariant; *)
          (* 2: takne by entailer, but was: the loop-condition expression type-checks (i.e., guarantees to evaluate successfully);*)
        - forward. forward.
        + EExists. entailer!.
         2: {
         EExists. entailer.
             } 
         + entailer!. 
     
        - repeat forward.
         + entailer!. split; try rep_lia. *)
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     
     (*Lemma le_sub_plus : forall x b_s p_s b_e p_e,
     0 <= x ->
     sem_cmp_pp Cle (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr x))) (Vptr b_e p_e) = Some (Vint Int.one) ->
     x <=  Ptrofs.unsigned (Ptrofs.sub p_e p_s).
     Proof. intros.
     induction x; try discriminate; try contradiction.
     - assert (Ptrofs.repr 0 = Ptrofs.zero) as H1 by auto. rewrite H1 in H0. assert (Ptrofs.add p_s Ptrofs.zero = p_s) as H2 by (apply Ptrofs.add_zero). 
         rewrite H2 in H0. unfold sem_cmp_pp in H0. simpl in H0.
         destruct (eq_block b_s b_e) eqn:e1; try discriminate; try contradiction.
         simpl in H. unfold negb in H. destruct (Ptrofs.ltu p_e p_s) eqn:e2; try discriminate; try contradiction.
         unfold Ptrofs.ltu in e2. 
         destruct (zlt (Ptrofs.unsigned p_e) (Ptrofs.unsigned p_s)); try contradiction; try discriminate.
         try rep_lia.
     - Search (Ptrofs.sub). unfold sem_cmp_pp in H0; simpl in H0. destruct (eq_block b_s b_e) eqn:e1; try contradiction; try discriminate.
         unfold negb, Ptrofs.ltu in H0; simpl in H0. destruct (zlt (Ptrofs.unsigned p_e)
         (Ptrofs.unsigned (Ptrofs.add p_s (Ptrofs.repr (Z.pos p))))) eqn:e2; try discriminate; try contradiction.
         unfold Ptrofs.sub. unfold Ptrofs.add in g. 
         assert (Hdiff: Ptrofs.unsigned p_e - Ptrofs.unsigned p_s
                      = Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned p_e - Ptrofs.unsigned p_s))). { Check Ptrofs.unsigned_repr. }
     Admitted.*)
     
     
     Lemma body_loop_1: semax_body Vprog Gprog f_loop_1 loop_1_spec.
     Proof. start_function. forward. 
         (*unfold abbreviate in POSTCONDITION. unfold abbreviate in MORE_COMMANDS.*)
         forward_loop 
             (EX n: Z, 
             PROP (
                 if pointer_le_bool (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE)))) (Vptr b_e p_e) 
                 then
                 0 <= (n+1) /\ PGSIZE * (n+1) <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) /\
                     (Int.min_signed <= Int.signed (Int.repr (n+1)) + Int.signed (Int.repr 1) <=
                     Int.max_signed)
                 else
                 0 <= n /\ PGSIZE * n <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) /\
                     (Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <=
                     Int.max_signed))
             LOCAL (temp _n (Vint (Int.repr n)); temp _pa_start (Vptr b_s p_s);
                     temp _pa_end (Vptr b_e p_e))
             SEP (denote_tc_test_order 
                     (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE))) 
                     (Vptr b_e p_e))) 
             break: 
             (EX n: Z,
             PROP (0 <= n /\ PGSIZE * n <= Ptrofs.unsigned (Ptrofs.sub p_e p_s))
             LOCAL (temp _n (Vint (Int.repr n)))
             SEP (denote_tc_test_order 
                     (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE))) 
                     (Vptr b_e p_e))).
         - Exists 0; entailer.
             destruct (pointer_le_bool (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE)))
             (Vptr b_e p_e)) eqn:e; entailer!. 
             unfold pointer_le_bool, pointer_cmp_bool, pointer_comparison in e.
             destruct (sem_cmp_pp Cle (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE))) (Vptr b_e p_e)) eqn:e1; try discriminate; try contradiction.
             destruct v; try discriminate; try contradiction.
             assert (i = Int.zero \/ i = Int.one) as H1. { apply cmp_le_is_either_0_or_1 with (p:= Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE))) (q:=Vptr b_e p_e); auto. }
             destruct H1; try discriminate; try contradiction.
             + rewrite H in e; inversion e.
             + rewrite H in e1. apply le_sub_plus in e1; auto.
             
             rewrite H in e1. unfold sem_cmp_pp in e1; simpl in e1. 
               destruct (eq_block b_s b_e); try discriminate; try contradiction.
               admit.
         - destruct (pointer_le_bool (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE))) (Vptr b_e p_e)) eqn:e; try discriminate; try contradiction.
             + Intros n. admit. 
             + Intros n. forward_if. forward. forward. EExists. entailer!.
     
             
             
             Search (Ptrofs.sub).
     
     
     
             + entailer!. unfold pointer_le_bool, pointer_cmp_bool, pointer_comparison in e.
               destruct (sem_cmp_pp Cle (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE)))
               (Vptr b_e p_e)) eqn:e1; try contradiction; try discriminate.
               destruct v; try contradiction; try discriminate.
               admit.
             + entailer.
                
             unfold pointer_cmp_bool in e. unfold 
             destruct (eq_dec
             (pointer_comparison (Vptr b_s (Ptrofs.add p_s (Ptrofs.repr PGSIZE))) 
                (Vptr b_e p_e) Cle) (Vint (Int.repr 1))) eqn:e2.
         - Intros n. forward_if.
             + forward. forward. EExists. entailer. split; auto. split; auto.  
     
         forward_loop
     
     
     (*Lemma body_loop_1: semax_body Vprog Gprog f_loop_1 loop_1_spec.
     Proof.
         start_function.
         forward. (*unfold abbreviate in POSTCONDITION.*)
         forward_loop (* inv = hold before and after the loop, break: post cond *)
         (EX sum: Z, EX p_s_val:ptrofs,
         PROP  (
                 (*0 <= sum /\ 
                 PGSIZE * sum <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) /\
                 Int.min_signed <= Int.signed (Int.repr sum) + Int.signed (Int.repr 1) <= Int.max_signed*)
                 )
         LOCAL (temp _n (Vint (Int.repr sum)); 
                temp _pa_start (Vptr b_s p_s_val);
                temp _pa_end (Vptr b_e p_e))
         SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s_val (Ptrofs.repr (PGSIZE)))))  (Vptr b_e p_e))) 
         break:
         (EX sum_final: Z, EX p_s_val:ptrofs,
         PROP ((*0 <= sum_final /\
               PGSIZE * sum_final <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) /\
               Int.min_signed <= Int.signed (Int.repr sum_final) <= Int.max_signed*)
             )
         LOCAL (temp _n (Vint (Int.repr sum_final)))
         SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s_val (Ptrofs.repr (PGSIZE)))))  (Vptr b_e p_e))).
         - Exists 0; EExists; entailer.
         - Intros sum. Intros p_s_val. forward_if.
             + forward. entailer. forward. Exists (sum). 
                 EExists . entailer!.
             split; auto.
                Admitted.*)
     
     
    

     (*Definition loop_1_spec : ident * funspec :=
    DECLARE _loop_1
    WITH b_s:block, p_s:ptrofs, b_e:block, p_e:ptrofs
    PRE [ tptr tvoid,tptr tvoid ]
        PROP ( )
        PARAMS (Vptr b_s p_s; Vptr b_e p_e)
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e))
    POST [ tint ]
        EX sum : Z,
        PROP ( )
        RETURN (Vint (Int.repr sum))
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e)).*)

(*Definition loop_1_spec : ident * funspec :=
    DECLARE _loop_1
    WITH b_s:block, p_s:ptrofs, b_e:block, p_e:ptrofs
    PRE [ tptr tvoid,tptr tvoid ]
        PROP (
            (*Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed*)
            )
        PARAMS (Vptr b_s p_s; Vptr b_e p_e)
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e))
    POST [ tint ]
        EX sum : Z,
        PROP (
              (*0 <= sum /\ 
              PGSIZE * sum <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) /\
              Int.min_signed <= Int.signed (Int.repr sum) <= Int.max_signed*)
        )
        RETURN (Vint (Int.repr sum))
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e)).*)

(*Definition loop_2_spec : ident * funspec :=
    DECLARE _loop_2
    WITH b_s:block, p_s:ptrofs, b_e:block, p_e:ptrofs
    PRE [ tptr tvoid,tptr tvoid ]
        PROP ( )
        PARAMS (Vptr b_s p_s; Vptr b_e p_e)
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e))
    POST [ tint ]
        EX sum : Z,
        PROP ( 0 <= sum <= Int.max_signed )
        RETURN (Vint (Int.repr sum))
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e)).*)




(*Nået hertil.. jeg skal have lavet min loop variant - og have fikset specifikationen, men den er jeg lidt i tvivl om*)
Lemma body_freerange_loop_1: semax_body Vprog Gprog f_freerange_loop_1 freerange_loop_1_spec.
Proof. start_function.
forward_loop 
(EX n: Z, 
PROP  (0 <= n /\ PGSIZE * n <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) /\
        Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed
        )
LOCAL (temp _n (Vint (Int.repr n)); temp _pa_start (Vptr b_s p_s);
       temp _pa_end (Vptr b_e p_e))
SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE)))))  (Vptr b_e p_e))) 
break:
(
PROP (0 <= n /\ PGSIZE * n <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) /\
        Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed
)
LOCAL (temp _n (Vint (Int.repr n)))
SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE)))))  (Vptr b_e p_e))).

Qed.