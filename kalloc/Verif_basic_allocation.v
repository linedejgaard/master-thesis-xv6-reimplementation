Require Import VST.floyd.proofauto.

Require Import VC.ASI_kalloc.
Require Import VC.kallocfun.
Require Import VC.Spec_kalloc.
Require Import VC.clientsfun.
Require Import VC.tactics.

Require Import VC.kalloc.



Local Open Scope logic.


Definition kalloc_write_42_spec : ident * funspec :=
    DECLARE _kalloc_write_42
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KF_globals gv sh ls xx original_freelist_pointer)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec original_freelist_pointer nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KF_globals gv  sh ls xx original_freelist_pointer * emp)
            else
            EX next ls',
                (!! (next :: ls' = ls /\
                    r = Vint (Int.repr 42)
                 ) &&
                    data_at sh tint (Vint (Int.repr 42)) original_freelist_pointer *
                    KF_globals gv  sh ls' xx next
            )
            )
        ).

Definition kalloc_int_array_spec : ident * funspec :=
    DECLARE _kalloc_int_array
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals, n:Z
    PRE [ tint ] 
    PROP (0 <= n /\ sizeof (tarray tint n) <= PGSIZE) (* make sure an array of size n fits into the page *)
    PARAMS(Vint (Int.repr n)) GLOBALS(gv) 
    SEP (KF_globals gv sh ls xx original_freelist_pointer)
    POST [ tptr tint ]
    PROP ( ) RETURN () SEP (
        (if eq_dec original_freelist_pointer nullval then
            KF_globals gv  sh ls xx original_freelist_pointer * emp
        else
        EX next ls',
            (!! (next :: ls' = ls) &&
                array_42_rep sh n original_freelist_pointer *
                KF_globals gv  sh ls' xx next
        )
        )
    ).

Definition kalloc_int_array_spec_fail : ident * funspec :=
    DECLARE _kalloc_int_array
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals, n:Z
    PRE [ tint ] 
    PROP (0 <= n <= Int.max_signed) PARAMS(Vint (Int.repr n)) GLOBALS(gv) SEP (KF_globals gv sh ls xx original_freelist_pointer)
    POST [ tptr tint ]
    PROP ( ) RETURN () SEP (
        (if eq_dec original_freelist_pointer nullval then
            KF_globals gv  sh ls xx original_freelist_pointer * emp
        else
        EX next ls',
            (!! (next :: ls' = ls) &&
                array_42_rep sh n original_freelist_pointer*
                KF_globals gv  sh ls' xx next
        )
        )
    ).

Lemma body_kalloc_write_42: semax_body KFVprog KFGprog f_kalloc_write_42 kalloc_write_42_spec.
Proof.
start_function.
forward. 
forward_call (kalloc_spec_sub KF_APD tint) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold KF_globals. entailer!.
- if_tac.
    + forward_if.
        * rewrite H in H0; auto_contradict.
        * forward. Exists (Vint(Int.repr 0)). entailer.
    + Intros ab.
      destruct ls; auto_contradict.
      forward_if.
        * unfold type_kalloc_token. rewrite kalloc_token_sz_split. Intros.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. forward.
        forward. forward.
        Exists (Vint(Int.repr 42)) (fst ab) (snd ab). entailer.
        * forward.
Qed.

Lemma body_kalloc_int_array: semax_body KFVprog KFGprog f_kalloc_int_array kalloc_int_array_spec.
Proof.
start_function.
forward.
forward_call (kalloc_spec_sub KF_APD (tarray tint n)) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold KF_globals. entailer!.
- destruct H; auto.
- if_tac.
    + forward_if.
        * rewrite H0 in H1; auto_contradict.
        * forward. 
    + Intros ab.
      destruct ls; auto_contradict.
      forward_if.
        * unfold type_kalloc_token. rewrite kalloc_token_sz_split. Intros.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq.
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
                KF_globals gv sh ls xx v
            )
            )
        )%assert.
        -- destruct H. unfold tarray in H7. rewrite sizeof_Tarray in H7. 
        assert (Z.max 0 n <= PGSIZE / (sizeof tint)). {  apply Zdiv_le_lower_bound. simpl; try rep_lia. auto. rewrite Z.mul_comm. auto. }
        assert (n <= PGSIZE / (sizeof tint)); try rep_lia. apply (Z.le_trans) with (PGSIZE / sizeof tint). try rep_lia.
        unfold PGSIZE; simpl; try rep_lia.
        -- entailer!. unfold tmp_array_42_rep. unfold KF_globals. entailer!. inversion H1; entailer.
        -- Intros.
        assert (Int.min_signed <= i <= Int.max_signed). { 
            assert (n <= Int.max_signed). {
            destruct H. unfold tarray in H7. unfold tarray in H8. rewrite sizeof_Tarray in H8. 
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
        rewrite Zlength_length in H13; try rep_lia.
        rewrite <- H13 at 1.
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
        rewrite H13; auto.
        ++ rewrite Zlength_app. rewrite array_42_length. rewrite Zlength_Zrepeat; try rep_lia.
        -- forward. Exists v ls. entailer!. unfold tmp_array_42_rep. unfold array_42_rep. 
        replace (n - n) with 0; try rep_lia. 
        rewrite Zrepeat_0. rewrite app_nil_r. entailer!.
    * forward.
Qed.

Lemma body_kalloc_int_array_fail: semax_body KFVprog KFGprog f_kalloc_int_array kalloc_int_array_spec_fail.
Proof.
start_function.
forward.
forward_call (kalloc_spec_sub KF_APD (tarray tint n)) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold KF_globals. entailer!.
- assert (exists n : Z, sizeof (tarray tint n) > PGSIZE). 
    {
        exists PGSIZE.
        split.
    }
    admit. (* this is not provable as n can be arbitrary large *)
Abort.
