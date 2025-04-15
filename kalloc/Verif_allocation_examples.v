Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.

Require Import VC.clientsfun.

Local Open Scope logic.


Definition kalloc_write_42_spec : ident * funspec :=
    DECLARE _kalloc_write_42
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) 
        SEP (KAF_globals gv sh ls xx original_freelist_pointer *
            if eq_dec original_freelist_pointer nullval then emp else
            (
            !! malloc_compatible (sizeof (tint)) original_freelist_pointer && emp (*&&
            memory_block sh (PGSIZE - (t_run_size)) (offset_val (t_run_size) original_freelist_pointer)*))
            )
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec original_freelist_pointer nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx original_freelist_pointer * emp)
            else
            EX next ls',
                (!! (next :: ls' = ls /\
                    r = Vint (Int.repr 42)
                 ) &&
                    data_at sh tint (Vint (Int.repr 42)) original_freelist_pointer *
                    memory_block sh (PGSIZE - sizeof tint)
                        (offset_val (sizeof tint) original_freelist_pointer) *
                    KAF_globals gv  sh ls' xx next
            )
            )
        ).

Definition kalloc_int_array_spec : ident * funspec :=
    DECLARE _kalloc_int_array
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals, n:Z
    PRE [ tint ] 
    PROP (0 < n /\ 0 < sizeof (tarray tint n) /\ sizeof (tarray tint n) <= PGSIZE) (* make sure an array of size n fits into the page *)
    PARAMS(Vint (Int.repr n)) GLOBALS(gv) 
    SEP (KAF_globals gv sh ls xx original_freelist_pointer *
    if eq_dec original_freelist_pointer nullval then emp else
    (
    !! malloc_compatible (sizeof (tarray tint n)) original_freelist_pointer &&
    memory_block sh (PGSIZE - (t_run_size)) (offset_val (t_run_size) original_freelist_pointer)))
    POST [ tptr tint ]
    PROP ( ) RETURN () SEP (
        (if eq_dec original_freelist_pointer nullval then
            KAF_globals gv  sh ls xx original_freelist_pointer * emp
        else
        EX next ls',
            (!! (next :: ls' = ls) &&
                array_42_rep sh n original_freelist_pointer *
                memory_block sh (PGSIZE - sizeof (tarray tint n))
                        (offset_val (sizeof (tarray tint n)) original_freelist_pointer) *
                KAF_globals gv  sh ls' xx next
        )
        )
    ).

Definition kalloc_write_pipe_spec : ident * funspec :=
    DECLARE _kalloc_write_pipe
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx original_freelist_pointer
        *
        if eq_dec original_freelist_pointer nullval then emp else
        (
        !! malloc_compatible (sizeof t_struct_pipe) original_freelist_pointer &&
        memory_block sh (PGSIZE - (t_run_size)) (offset_val (t_run_size) original_freelist_pointer)))
    POST [ tvoid ]
        PROP ( ) RETURN () SEP (
            (if eq_dec original_freelist_pointer nullval then
                KAF_globals gv  sh ls xx original_freelist_pointer *emp
            else
            EX next ls',
                (!! (next :: ls' = ls) &&
                    pipe_rep sh original_freelist_pointer *
                    memory_block sh (PGSIZE - sizeof (t_struct_pipe))
                    (offset_val (sizeof (t_struct_pipe)) original_freelist_pointer) *
                    KAF_globals gv  sh ls' xx next
            )
            )
        ).
       

Definition kalloc_int_array_spec_fail : ident * funspec :=
    DECLARE _kalloc_int_array
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals, n:Z
    PRE [ tint ] 
    PROP (0 < n <= Int.max_signed) PARAMS(Vint (Int.repr n)) GLOBALS(gv) 
    SEP (KAF_globals gv sh ls xx original_freelist_pointer *
    if eq_dec original_freelist_pointer nullval then emp else
    (
    !! malloc_compatible (sizeof (tarray tint n)) original_freelist_pointer &&
    memory_block sh (PGSIZE - (t_run_size)) (offset_val (t_run_size) original_freelist_pointer)))
    POST [ tptr tint ]
    PROP ( ) RETURN () SEP (
        (if eq_dec original_freelist_pointer nullval then
            KAF_globals gv  sh ls xx original_freelist_pointer * emp
        else
        EX next ls',
            (!! (next :: ls' = ls) &&
                array_42_rep sh n original_freelist_pointer*
                memory_block sh (PGSIZE - sizeof (tarray tint n))
                        (offset_val (sizeof (tarray tint n)) original_freelist_pointer) *
                KAF_globals gv  sh ls' xx next
        )
        )
    ).

Lemma body_kalloc_write_42: semax_body KAFVprog KAFGprog f_kalloc_write_42 kalloc_write_42_spec.
Proof.
start_function.
Intros.
forward. if_tac_auto_contradict. 
- forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
+ unfold KAF_globals. entailer!.
+ if_tac_auto_contradict.
    * forward_if.
        -- rewrite H in H1; auto_contradict.
        -- forward. Exists (Vint(Int.repr 0)). entailer.
- forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
    + unfold KAF_globals. entailer!. (*if_tac_auto_contradict. entailer!.*)
    + if_tac_auto_contradict.
    Intros ab.
      destruct ls; auto_contradict.
      forward_if.
        * unfold type_kalloc_token. rewrite kalloc_token_sz_split.
        destruct original_freelist_pointer eqn:eo; inversion H2.
        rewrite token_merge with (b:= b) (i:= i); auto.
        Intros.
        assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE). { try rep_lia. }
        rewrite <- H14.
        destruct original_freelist_pointer; auto_contradict.
        assert (i = Ptrofs.repr (Ptrofs.unsigned i)). { rewrite Ptrofs.repr_unsigned. auto. }
        rewrite H15 at 2.
        rewrite memory_block_split with (sh := sh) (n:=(sizeof tint)) (m :=(PGSIZE - sizeof tint)) (b := b); try rep_lia.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
        rewrite <- H15.
        forward. forward. forward.
        Exists (Vint(Int.repr 42)) (fst ab) (snd ab). entailer.
        rewrite <- H15. auto.
        admit. (* this should be provable if it wasn't for the ";" symbol *)
        * forward.
Admitted.



Lemma body_kalloc_int_array: semax_body KAFVprog KAFGprog f_kalloc_int_array kalloc_int_array_spec.
Proof.
start_function.
Intros.
forward. if_tac_auto_contradict; destruct H as [HH1 HH2].
- forward_call (kalloc_spec_sub KAF_APD (tarray tint n)) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
+ unfold KAF_globals. entailer!.
+ if_tac_auto_contradict.
    * forward_if.
        -- rewrite H in H1; auto_contradict.
        -- forward.
- forward_call (kalloc_spec_sub KAF_APD (tarray tint n)) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
    + unfold KAF_globals. if_tac_auto_contradict. entailer!.
    + if_tac_auto_contradict.
    Intros ab.
      destruct ls; auto_contradict.
      forward_if.
        * unfold type_kalloc_token. rewrite kalloc_token_sz_split. Intros.
        assert (sizeof (tarray tint n) + (PGSIZE - sizeof (tarray tint n)) = PGSIZE). { try rep_lia. }
        forward_for_simple_bound n
        (EX i:Z,
        PROP  ()
        LOCAL (
            temp _pa original_freelist_pointer; gvars gv;
            temp _n (Vint (Int.repr n))
            ) 
        SEP (
            (
                tmp_array_42_rep sh n original_freelist_pointer i*
                memory_block sh (PGSIZE - sizeof (tarray tint n))
                        (offset_val (sizeof (tarray tint n)) original_freelist_pointer) *
                KAF_globals gv sh ls xx v
            )
            )
        )%assert.
        -- destruct HH2 as [HH2 HH3]. unfold tarray in HH3. rewrite sizeof_Tarray in HH3. 
        assert (Z.max 0 n <= PGSIZE / (sizeof tint)). {  apply Zdiv_le_lower_bound. simpl; try rep_lia. auto. rewrite Z.mul_comm. auto. }
        assert (n <= PGSIZE / (sizeof tint)); try rep_lia. apply (Z.le_trans) with (PGSIZE / sizeof tint). try rep_lia.
        unfold PGSIZE; simpl; try rep_lia.
        -- entailer. unfold tmp_array_42_rep. unfold KAF_globals. entailer. inversion H1; entailer.
        destruct original_freelist_pointer; auto_contradict.
        assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH12. { rewrite Ptrofs.repr_unsigned. auto. }
        assert (Zrepeat (default_val tint) n = default_val (tarray tint n)) as Hdefault. {
            apply Zrepeat_default_val_array. auto.
        }
        rewrite HH12 at 1.
        rewrite <- H10 at 1.
        rewrite memory_block_split with (m:=(PGSIZE - sizeof (tarray tint n))); try rep_lia.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. 
        entailer!. simpl. entailer!.
        rewrite <- H12.
        rewrite H12.
        rewrite Hdefault.
        entailer!. 
        rewrite Ptrofs.repr_unsigned. auto.
        -- Intros.
        assert (Int.min_signed <= i <= Int.max_signed). { 
            assert (n <= Int.max_signed). {
            destruct HH2 as [HH2 HH3]. 
            unfold tarray in HH3. unfold tarray in HH3. rewrite sizeof_Tarray in HH3. 
            assert (Z.max 0 n <= PGSIZE / (sizeof tint)). {  apply Zdiv_le_lower_bound. simpl; try rep_lia. auto. rewrite Z.mul_comm. auto. }
            assert (n <= PGSIZE / (sizeof tint)); try rep_lia. apply (Z.le_trans) with (PGSIZE / sizeof tint). try rep_lia.
            unfold PGSIZE; simpl; try rep_lia.
            }
            split; try rep_lia.
        } unfold tmp_array_42_rep.
        forward. entailer.
        unfold tmp_array_42_rep. entailer!. 
        rewrite upd_Znth_unfold.
        ++ rewrite sublist_firstn. 
        rewrite firstn_app1.
        assert (Zlength (array_42 (Z.to_nat i)) = i). { rewrite array_42_length. try rep_lia. }
        rewrite Zlength_length in H21; try rep_lia.
        rewrite <- H21 at 1.
        rewrite firstn_exact_length with (xs :=array_42 (Z.to_nat i)); try rep_lia.
        rewrite sublist_app2.
        rewrite array_42_length.
        replace (i + 1 - Z.of_nat (Z.to_nat i)) with (1); try rep_lia.
        rewrite Zlength_app.
        rewrite array_42_length.
        replace (Z.of_nat (Z.to_nat i) + Zlength (Zrepeat (default_val tint) (n - i)) -
        Z.of_nat (Z.to_nat i)) with (Zlength (Zrepeat (default_val tint) (n - i))); try rep_lia.
        rewrite Zlength_Zrepeat; try rep_lia.
        rewrite sublist_Zrepeat; try rep_lia.
        replace (Z.to_nat (i + 1)) with (Z.to_nat (i) + 1)%nat; try rep_lia.
        rewrite <- array_42_append.
        replace (n - i - 1) with (n - (i + 1)); try rep_lia. 
        rewrite app_assoc. entailer!.
        ** rewrite array_42_length. try rep_lia.
        ** assert (Datatypes.length (array_42 (Z.to_nat i))%nat = Z.to_nat i). {
            rewrite <- Zlength_length; try rep_lia.
            rewrite array_42_length.
            try rep_lia.
        }
        rewrite H21; auto.
        ++ rewrite Zlength_app. rewrite array_42_length. rewrite Zlength_Zrepeat; try rep_lia.
        -- forward. Exists v ls. entailer!. unfold tmp_array_42_rep. unfold array_42_rep. 
        replace (n - n) with 0; try rep_lia. 
        rewrite Zrepeat_0. rewrite app_nil_r. entailer!.
    * forward.
Qed.

Lemma body_kalloc_int_array_fail: semax_body KAFVprog KAFGprog f_kalloc_int_array kalloc_int_array_spec_fail.
Proof.
start_function. Intros.
forward.
forward_call (kalloc_spec_sub KAF_APD (tarray tint n)) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold KAF_globals. if_tac.
+ entailer!.
+ entailer!.
- assert (exists n : Z, sizeof (tarray tint n) > PGSIZE). 
    {
        exists PGSIZE.
        split.
    }
    admit. (* this is not provable as n can be arbitrary large *)
Abort.

Lemma body_kalloc_write_pipe: semax_body KAFVprog KAFGprog f_kalloc_write_pipe kalloc_write_pipe_spec.
Proof.
start_function.
Intros.
forward.
forward_call (kalloc_spec_sub KAF_APD t_struct_pipe) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold KAF_globals. entailer!. 
- if_tac. (*destruct (eq_dec original_freelist_pointer nullval) eqn:e0.*)
    + forward_if.
        * rewrite H in H0; auto_contradict.
        * forward. entailer.
    + Intros ab. forward_if.
        *
        rewrite mem_mgr_split. rewrite type_kalloc_token_split. Intros. rewrite kalloc_token_sz_split.
        Intros.
        assert (sizeof (t_struct_pipe) + (PGSIZE - sizeof (t_struct_pipe)) = PGSIZE) as HH12. { try rep_lia. }
        rewrite <- HH12.
        destruct original_freelist_pointer; auto_contradict.
        assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HHH12. { rewrite Ptrofs.repr_unsigned. auto. }
        rewrite HHH12.
        rewrite memory_block_split with (m:=(PGSIZE - sizeof t_struct_pipe)); try rep_lia.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
        forward. forward. forward. forward.
        entailer.
        Exists  (fst ab) (snd ab). entailer.
        unfold KAF_globals. unfold pipe_rep.  Exists (fst (default_val t_struct_pipe)). entailer!.
        rewrite mem_mgr_split. 
        assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH0. { rewrite Ptrofs.repr_unsigned. auto. }
        rewrite <- HH0.
        entailer!.
        assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH0. { rewrite Ptrofs.repr_unsigned. auto. }
        rewrite <- HH0.
        auto. try simpl; rep_lia.
        try simpl; rep_lia.
        * forward.
        entailer!.
Qed.
