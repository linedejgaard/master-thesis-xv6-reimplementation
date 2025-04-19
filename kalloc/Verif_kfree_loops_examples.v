Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.ASI_kalloc.
Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.

Require Import VC.clientsfun.

Local Open Scope logic.

Definition kfree_kfree_kalloc_loop_spec := 
    DECLARE _kfree_kfree_kalloc_loop
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            isptr pa1 /\ (* just assume it is pointers for simplicity *)
            Int.min_signed <= Int.signed (Int.repr 2) + Int.signed (Int.repr 1) <= Int.max_signed
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (2)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (offset_val PGSIZE pa1) (* we return the head like in the pop function*)
            SEP 
            (
                (*data_at sh t_run pa1 (offset_val PGSIZE pa1) **)
                kalloc_token' KAF_APD sh (sizeof t_run) (offset_val PGSIZE pa1) *
                KAF_globals gv sh (orig_head::ls) xx pa1
                ).

Definition kfree_loop_spec := 
    DECLARE _kfree_loop
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tvoid ]
        EX head, EX added_elem, (* TODO: fix top and next is the same?? *)
        PROP( 
            added_elem = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE orig_head) /\
            head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE orig_head)++ls))
            )
            RETURN () (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv sh (added_elem++ls) xx head
            ).

Definition kfree_loop_kalloc_spec := 
    DECLARE _kfree_loop_kalloc
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KAF_globals gv sh ls xx orig_head
        )
    POST [ tptr tvoid ]
        EX head, EX added_elem, (* TODO: fix top and next is the same?? *)
        PROP( 
            (* before alloc *)
            added_elem = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE orig_head) /\
            head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE orig_head)++ls))
            )
            RETURN (head) (* we return the head like in the pop function*)
            SEP 
            (
            let n_eq_0_case :=
                if eq_dec orig_head nullval then
                emp * KAF_globals gv sh ls xx orig_head
            else
                EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) orig_head
            in
            let n_gt_0_case :=
                KAF_globals gv sh ((tl added_elem)++ls) xx (hd nullval added_elem) *
                kalloc_token' KAF_APD sh (sizeof t_run) head
            in
            if (Z.ltb 0 n) then
                n_gt_0_case
            else 
                n_eq_0_case
                ).


Definition KAFGprog_clients: funspecs := KAFGprog ++ [kfree_loop_spec].


Lemma body_kfree_kfree_kalloc_loop: semax_body  KAFVprog KAFGprog f_kfree_kfree_kalloc_loop kfree_kfree_kalloc_loop_spec.
Proof.
    start_function.
    Intros. forward. (*forward. unfold abb iate in POSTCONDITION.*)
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= 2 /\
        ((curr_head = orig_head /\ i = 0) \/ (curr_head = (offset_val (-PGSIZE) (p_tmp))  /\ i <> 0)) /\
        tmp_added_elem = (pointers_with_original_head (Z.to_nat i) (pa1) PGSIZE orig_head) /\
        p_tmp = offset_val (i * PGSIZE)%Z pa1 /\
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
        (
        KAF_globals gv sh (tmp_added_elem ++ ls) xx curr_head *
        kalloc_tokens Tok_APD sh (Z.to_nat(2-i)) p_tmp (PGSIZE) t_run
        )
        )
    )%assert; destruct H as [H H3].
    - entailer. Exists 0 pa1 orig_head (pointers_with_original_head (Z.to_nat 0) pa1 PGSIZE orig_head). (*entailer. *)
        rewrite <- pointers_with_head_empty. simpl; entailer!; unfold offset_val in H2; destruct pa1; auto_contradict.
    - entailer.
    - Intros. destruct (Z.to_nat (2 - i)) eqn:e.
        +assert (i = 2); try rep_lia.
        + forward_call (kfree_spec_sub KAF_APD t_run) (p_tmp, gv, sh , (tmp_added_elem ++ ls), xx,curr_head). (* call kfree*)
            * if_tac; destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
                -- unfold offset_val in H1. destruct pa1; auto_contradict.
                --unfold KAF_globals. unfold type_kalloc_token. rewrite kalloc_token_sz_split. simpl. rewrite kalloc_token_sz_split. Intros.
                simpl. 
                entailer!.
            * destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04. unfold is_pointer_or_null.
              unfold offset_val. destruct pa1; auto_contradict; auto.
            * forward. entailer!. destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04. unfold is_pointer_or_null.
            unfold offset_val. destruct pa1; auto_contradict; auto.
            forward. if_tac; auto_contradict; destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
                -- unfold offset_val in H1. destruct pa1; auto_contradict.
                -- Exists ((((i+1)%Z, (offset_val PGSIZE p_tmp):val), p_tmp:val), (curr_head::(pointers_with_original_head(Z.to_nat (i)) pa1 PGSIZE)orig_head):list val).
                entailer!. 
                ++ split; try rep_lia. split.
                    ** right. split; try rep_lia. replace (i * PGSIZE + PGSIZE + - PGSIZE) with (i * PGSIZE)%Z; try rep_lia.
                    auto.
                    ** split.
                        --- destruct H02 as [[H0211 H0212] | [H0221 H0222]].
                            +++ rewrite H0212. simpl. rewrite H0211. auto.
                            +++ rewrite sub_add_offset_n in H0221; auto; try rep_lia.
                            2: {
                            unfold PGSIZE; try rep_lia.
                            }
                            rewrite H0221.
                            replace (i - 1) with (Z.of_nat ((Z.to_nat i) - 1)%nat); try rep_lia.
                            replace (Z.to_nat (i + 1)) with (((Z.to_nat i) + 1)%nat); try rep_lia.
                            rewrite add_to_pointers_with_head; auto; try rep_lia.
                        --- replace (i * PGSIZE + PGSIZE) with ((i + 1) * PGSIZE)%Z; try rep_lia; auto.
                ++ unfold KAF_globals. 
                assert (Z.to_nat (2 - (i + 1)) = n); try rep_lia.
                rewrite H6. rewrite app_comm_cons. entailer!.
    - forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , pa1::orig_head::ls, xx, offset_val PGSIZE pa1). (* kalloc *)
        +
        (*- forward_call (sh, add_offset pa1 PGSIZE, xx, (pa1::orig_head::ls), gv). (* call kalloc *)*)
        entailer. destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
        unfold KAF_globals. rewrite H03.
        rewrite mem_mgr_split.
         
        assert (i = 2); try rep_lia. rewrite H0. destruct (0 <? Z.to_nat 2)%nat eqn:ei; try rep_lia.
        * destruct H02 as [[H021 H022] | [H031 H032]]; try rep_lia.
          rewrite H04 in H031. rewrite sub_add_offset_n in H031; auto; try rep_lia.
          Intros.
          destruct (Z.to_nat 2) eqn:e2; auto_contradict.
          unfold pointers_with_original_head.
          destruct n eqn:en; try rep_lia.
          destruct n0 eqn:en0; try rep_lia.
          simpl. rewrite mem_mgr_split. refold_freelistrep. entailer!. entailer!.
          unfold PGSIZE; rep_lia.
        * rewrite Nat.ltb_ge in ei. try rep_lia.
        + destruct H0 as [H01 [H02 [H03 [H04 H05]]]].
        forward. if_tac.
        assert (isptr (offset_val PGSIZE pa1)). {
            apply isptr_offset_val'; auto.
        }
        rewrite H1 in H2; auto_contradict.
        Intros ab. unfold type_kalloc_token, KAF_globals. 
        inversion H2. entailer!.
Qed.


Lemma body_kfree_loop: semax_body KAFVprog KAFGprog f_kfree_loop kfree_loop_spec.
Proof.
start_function.
Intros. forward. (*forward. unfold abb iate in POSTCONDITION.*)
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= n /\
        ((curr_head = orig_head /\ i = 0) \/ (curr_head = (offset_val (-PGSIZE) (p_tmp))  /\ i <> 0)) /\
        tmp_added_elem = (pointers_with_original_head (Z.to_nat i) (pa1) PGSIZE orig_head) /\
        p_tmp = offset_val (i * PGSIZE)%Z pa1 /\
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
        (
            KAF_globals gv sh (tmp_added_elem ++ ls) xx curr_head *
            kalloc_tokens Tok_APD sh (Z.to_nat(n-i)) p_tmp (PGSIZE) t_run
        )
    ))%assert; destruct H as [H01 [H02 H03]].
    - entailer. Exists 0 pa1 orig_head (pointers_with_original_head (Z.to_nat 0) pa1 PGSIZE orig_head). (*entailer. *)
        rewrite <- pointers_with_head_empty. entailer. destruct (Z.to_nat n).
            + rewrite <- H0 in H01. try rep_lia.
            + rewrite app_nil_l. entailer!.
    - entailer.
    - Intros. destruct (Z.to_nat (n - i)) eqn:e1.
        + try rep_lia.
        + forward_call (kfree_spec_sub KAF_APD t_run) (p_tmp, gv, sh , (tmp_added_elem ++ ls), xx,curr_head). (* call kfree*)
        (*forward_call (sh, p_tmp, curr_head, xx, gv, (tmp_added_elem ++ ls), PGSIZE). (* call kfree1 *)*)
            *if_tac; destruct H0 as [H001 [H002 [H003 [H04 H05]]]]. rewrite H04 in H.
            -- unfold offset_val in H. destruct pa1; auto_contradict.
            --unfold KAF_globals. unfold type_kalloc_token. rewrite kalloc_token_sz_split. simpl. rewrite kalloc_token_sz_split. Intros.
            simpl. entailer!. 
            * destruct H0 as [H001 [H002 [H003 [H04 H05]]]]. rewrite H04.
                assert ( isptr (offset_val (i * PGSIZE) pa1)). {apply isptr_offset_val'. auto. }
                auto.
            * forward. 
                --entailer!. destruct H0 as [H001 [H002 [H003 [H04 H05]]]]. rewrite H04.
                assert ( isptr (offset_val (i * PGSIZE) pa1)). {apply isptr_offset_val'. auto. }
                auto.
                -- forward. if_tac_auto_contradict.
                ++ destruct H0 as [H001 [H002 [H003 [H04 H05]]]]. rewrite H04.
                assert ( isptr (p_tmp)). { rewrite H04. apply isptr_offset_val'. auto. }
                rewrite H in H0; auto_contradict.
                ++ Exists ((((i+1)%Z, (offset_val PGSIZE p_tmp):val), p_tmp:val), ((pointers_with_original_head(Z.to_nat (i+1)) pa1 PGSIZE)orig_head):list val).
                entailer!; destruct H0 as [H001 [H002 [H003 [H04 H05]]]].
                    **simpl. do 2 split; try rep_lia. split. 
                        --- right. split. rewrite isptr_offset_val_zero; auto.
                        rewrite H04. apply isptr_offset_val'. auto.
                        destruct H002 as [[H0021 H0022] | [H0021 H0022]]; try rep_lia.
                        --- split.
                        destruct (Z.to_nat i) eqn:ei.
                        destruct H002 as [[H0021 H0022] | [H0021 H0022]]; try rep_lia.
                        rewrite H04. rewrite H0022. unfold PGSIZE; auto. simpl. rewrite isptr_offset_val_zero; auto.
                         rewrite <- add_add_offset_n; auto; try rep_lia.
                         rewrite H04. auto.
                         unfold PGSIZE; rep_lia.
                        assert (n + 1 <= Int.max_signed); try rep_lia.
                        rewrite Int.signed_repr in H02; try rep_lia. rewrite Int.signed_repr in H02; try rep_lia.
                        --- rewrite sem_add_pi'; auto. rewrite H04. apply isptr_offset_val'. auto.
                        try rep_lia.
                    ** unfold KAF_globals.
                    assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia.
                    rewrite H0.
                    assert (curr_head :: tmp_added_elem = pointers_with_original_head (Z.to_nat (i + 1)) pa1 PGSIZE orig_head). {
                        rewrite H003.
                        destruct H002 as [[H0021 H0022] | [H0021 H0022]].
                        - rewrite H0022. simpl. rewrite H0021. auto.
                        - replace (Z.to_nat (i + 1)) with (((Z.to_nat i) + 1)%nat); try rep_lia.
                        rewrite <- add_to_pointers_with_head; auto.
                        rewrite H0021; rewrite H04.
                        rewrite sub_add_offset_n; auto; try rep_lia.
                        replace (Z.of_nat (Z.to_nat i - 1))%Z with ((i - 1))%Z; try rep_lia.
                        auto.
                        unfold PGSIZE; rep_lia.
                        try rep_lia.
                    }
                    rewrite app_comm_cons.
                    rewrite H5. entailer!.
    - forward.  Exists curr_head tmp_added_elem. entailer.
    destruct H0 as [H001 [H002 [H003 [H04 H05]]]].
    destruct (Z.to_nat (n - i)) eqn:eni; try rep_lia.
    simpl. entailer!.
    split. assert (i = n); try rep_lia. rewrite H2. auto.
    destruct (Z.to_nat n) eqn:en; destruct H002 as [[H0021 H0022] | [H0021 H0022]]; try rep_lia.
    + simpl. auto.
    + rewrite <- add_to_pointers_with_head; auto; try rep_lia. simpl.
    rewrite H0021.  rewrite sub_add_offset_n; auto; try rep_lia.
    replace (Z.of_nat (n0 - 0)) with (i -1); try rep_lia. auto.
    unfold PGSIZE; rep_lia.
Qed.


Lemma body_kfree_loop_kalloc: semax_body KAFVprog KAFGprog_clients f_kfree_loop_kalloc kfree_loop_kalloc_spec.
Proof.
start_function.
forward_call (sh, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, n:Z).
- destruct H as [H1 [H2 H3]]; auto.
- Intros vret. 
forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , snd vret ++ ls, xx,  fst vret ); (* kalloc *)
destruct H as [H11 [H12 H13]]; auto.
    + unfold KAF_globals. entailer!.
    + if_tac; auto_contradict.
        * forward. destruct (Z.to_nat n) eqn:en.
            -- assert (n = 0); try rep_lia. rewrite H3. Exists (fst vret) (snd vret).
                    entailer.
                    if_tac_auto_contradict;
                    destruct (0 <? 0) eqn:efalse; try rep_lia.
                ++simpl in H0. rewrite H0. simpl in H1. rewrite H1. unfold KAF_globals. rewrite app_nil_l. entailer!.
                ++simpl in H1. rewrite <- H1 in H3. rewrite H in H3; auto_contradict.
            -- rewrite <- add_to_pointers_with_head in H1; auto; try rep_lia. simpl in H1.
            assert (isptr (offset_val (Z.of_nat (n0 - 0) * PGSIZE) pa1)). { apply isptr_offset_val'. auto. }
            rewrite <- H1 in H3. rewrite H in H3; auto_contradict.
        * forward. destruct (Z.to_nat n) eqn:en.
            -- Exists (fst vret) (snd vret).
                assert (n = 0) as HH5; try rep_lia. rewrite HH5.
                if_tac_auto_contradict;
                destruct (0 <? 0) eqn:efalse; try rep_lia.
                ++ unfold KAF_globals. entailer!.
                ++ destruct ls eqn:els.
                    **  simpl in H0. rewrite H0 in H3. inversion H3.
                    ** simpl in H1. simpl in H0. Exists (fst ab) (snd ab). unfold KAF_globals. rewrite H1.
                    entailer!. rewrite H0 in H3. rewrite app_nil_l in H3. auto.
                    unfold type_kalloc_token. entailer!.
            -- Exists (fst vret) (snd vret).
                entailer.
                destruct (0 <? n) eqn:etrue; try rep_lia.
                unfold KAF_globals. unfold type_kalloc_token. entailer!.
                destruct (snd vret).
                ++ replace (S n0) with (n0 + 1)%nat in H0; try rep_lia. 
                destruct n0 eqn:en0.
                ** simpl in H0. inversion H0.
                ** rewrite  <- add_to_pointers_with_head in H0; auto; try rep_lia. inversion H0.
                ++ simpl. rewrite <- app_comm_cons in H3. inversion H3. entailer.
Qed.