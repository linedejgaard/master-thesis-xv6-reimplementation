Require Import VST.floyd.proofauto.

Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.tactics.

Require Import VC.ASI_kalloc.
Require Import VC.Kalloc_APD.
Require Import VC.Spec_kalloc.

Require Import VC.clientsfun.

Local Open Scope logic.


Definition kfree_kalloc_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, orig_head:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(is_pointer_or_null new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec new_head nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) new_head))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP( 
            ((new_head = nullval) /\ ( orig_head = nullval) /\ r = nullval) \/
            ((new_head <> nullval) /\  r = new_head) \/
            ((new_head = nullval) /\ ( orig_head <> nullval) /\ r = orig_head)
        )
        RETURN (r) (* we return the head like in the pop function*)
        SEP (
            let freelist_case :=
            if eq_dec orig_head nullval then
            emp * KAF_globals gv sh ls xx orig_head
            else
            EX next, EX ls',
                !! (next :: ls' = ls) &&
                KAF_globals gv sh ls' xx next *
                kalloc_token' KAF_APD sh (sizeof t_run) orig_head
        in
        
        let newhead_case :=
            KAF_globals gv sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) new_head
        in
        
        if eq_dec new_head nullval then
            freelist_case
        else
            newhead_case
).


Definition kfree_kalloc_inverses_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, orig_head:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(isptr new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) new_head
        )
    POST [ tptr tvoid ]
        PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            KAF_globals gv sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) new_head
    ).


Definition kalloc_kfree_inverses_spec : ident * funspec :=
    DECLARE _kalloc_kfree
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tvoid ] 
        PROP ( ) RETURN () 
        SEP (
            KAF_globals gv sh ls xx orig_head
        ).

Definition kalloc_write_42_kfree_spec : ident * funspec :=
    DECLARE _kalloc_write_42_kfree
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec orig_head nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx orig_head)
            else
                (!! ( r = Vint (Int.repr 42) ) &&
                KAF_globals gv  sh ls xx orig_head)
            )
        ).

Definition kalloc_write_40_2_kfree_spec : ident * funspec :=
    DECLARE _kalloc_write_40_2_kfree
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx orig_head)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec orig_head nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx orig_head)
            else
                if (Nat.ltb 1 (length ls)) then
                    (!! ( r = Vint (Int.repr 42) ) &&
                    KAF_globals gv  sh ls xx orig_head)
                else 
                    (!! ( r = Vint (Int.repr 40) ) &&
                    KAF_globals gv  sh ls xx orig_head)
            )
        ).
        
Definition kfree_kalloc_twice_spec:= 
    DECLARE _kfree_kalloc_twice
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls:list val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head <> nullval) /\ (r = orig_head)) \/ (* then there is exists a value or null in ls that is returned *)
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head <> nullval)) (* r is either nullval or next next*)
            ) 
            RETURN (r) (* we return the head like in the pop function*)
            SEP 
            (
                let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                (if eq_dec orig_head nullval then
                    KAF_globals gv sh ls xx orig_head * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) orig_head)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec orig_head nullval then 
                        KAF_globals gv sh ls xx orig_head * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KAF_globals gv sh ls' xx next *
                        kalloc_token' KAF_APD sh (sizeof t_run) orig_head) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec orig_head nullval then
                        emp * KAF_globals gv sh ls xx orig_head
                    else
                        (kalloc_token' KAF_APD sh (sizeof t_run) orig_head *
                        (EX next1, EX ls1,
                        !! (next1:: ls1 = ls) &&
                        if eq_dec next1 nullval then
                            KAF_globals gv sh ls1 xx next1
                        else (
                        EX next2, EX ls2,
                        !! (next2:: ls2 = ls1) &&
                        KAF_globals gv sh ls2 xx next2 * 
                        kalloc_token' KAF_APD sh (sizeof t_run) next1
                        )))
                in
                let both_pointers_case :=
                KAF_globals gv sh ls xx orig_head *
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
                in
                if eq_dec pa1 nullval then
                    if eq_dec pa2 nullval then
                        freelist_both_null_case
                    else freelist_only_pa1_null_case
                else 
                    if eq_dec pa2 nullval then
                        freelist_only_pa2_null_case
                    else both_pointers_case
).


Definition kfree_kalloc_kfree_kalloc_spec:= 
    DECLARE _kfree_kalloc_kfree_kalloc
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls:list val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (orig_head <> nullval) /\ (r = orig_head)) \/ (* then there is exists a value or null in ls that is returned *)
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( orig_head <> nullval)) (* r is either nullval or next next*)
            ) 
            RETURN (r) (* we return the head like in the pop function*)
            SEP 
            (
                let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                (if eq_dec orig_head nullval then
                    KAF_globals gv sh ls xx orig_head * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) orig_head)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec orig_head nullval then 
                        KAF_globals gv sh ls xx orig_head * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KAF_globals gv sh ls' xx next *
                        kalloc_token' KAF_APD sh (sizeof t_run) orig_head) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec orig_head nullval then
                        emp * KAF_globals gv sh ls xx orig_head
                    else
                        (kalloc_token' KAF_APD sh (sizeof t_run) orig_head *
                        (EX next1, EX ls1,
                        !! (next1:: ls1 = ls) &&
                        if eq_dec next1 nullval then
                            KAF_globals gv sh ls1 xx next1
                        else (
                        EX next2, EX ls2,
                        !! (next2:: ls2 = ls1) &&
                        KAF_globals gv sh ls2 xx next2 * 
                        kalloc_token' KAF_APD sh (sizeof t_run) next1
                        )))
                in
                let both_pointers_case :=
                KAF_globals gv sh ls xx orig_head *
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
                in
                if eq_dec pa1 nullval then
                    if eq_dec pa2 nullval then
                        freelist_both_null_case
                    else freelist_only_pa1_null_case
                else 
                    if eq_dec pa2 nullval then
                        freelist_only_pa2_null_case
                    else both_pointers_case
).

Definition kfree_kfree_kalloc_spec :=
    DECLARE _kfree_kfree_kalloc
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ r = orig_head) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ r = pa1) \/
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2)
        )
        RETURN (r) (* we return the head like in the pop function*)
        SEP 
        (
            let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                KAF_globals gv sh ls xx orig_head
            in
            let freelist_only_pa2_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                KAF_globals gv sh ls xx orig_head
            in
            let freelist_both_null_case :=
                if eq_dec orig_head nullval then
                    emp * KAF_globals gv sh ls xx orig_head
                else
                    (EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) orig_head)
            in
            let both_is_pointers_case :=
                KAF_globals gv sh (orig_head::ls) xx pa1 *
                (*kalloc_token' KAF_APD sh (sizeof t_run) pa1 *)
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
            in
            if eq_dec pa1 nullval then
                if eq_dec pa2 nullval then
                    freelist_both_null_case
                else freelist_only_pa1_null_case
            else 
                if eq_dec pa2 nullval then
                    freelist_only_pa2_null_case
                else both_is_pointers_case
        ).



Definition kalloc_write_42_kfree_kfree_spec : ident * funspec :=
    DECLARE _kalloc_write_42_kfree_kfree
    WITH sh : share, orig_head:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) 
        SEP (KAF_globals gv sh ls xx orig_head )
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec orig_head nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx orig_head)
            else
                (!! ( r = Vint (Int.repr 42) ) &&
                KAF_globals gv  sh ls xx orig_head)
            )
        ).

Definition kfree_kfree_kalloc_kalloc_spec := 
    DECLARE _kfree_kfree_kalloc_kalloc
    WITH sh : share, pa1:val, pa2:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            isptr pa1 /\
            isptr pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
            kalloc_token' KAF_APD sh (sizeof t_run) pa2
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv  sh ls xx orig_head *
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
                ).

Definition kfree_kfree_same_pointer_wrong_spec := 
    DECLARE _kfree_kfree_same_pointer
    WITH sh : share, pa1:val, orig_head:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            isptr pa1
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx orig_head *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1
            )
    POST [ tvoid ]
        PROP( )
            RETURN () (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv  sh (pa1::orig_head::ls) xx pa1
            ).

Definition KAFGprog_clients: funspecs := KAFGprog ++ [kfree_kalloc_spec].

Ltac simplify_kalloc_token :=
    repeat (
    rewrite kalloc_token_sz_split;
    unfold type_kalloc_token
    );
entailer!.


Lemma body_kfree_kalloc: semax_body KAFVprog KAFGprog f_kfree_kalloc kfree_kalloc_spec.
Proof.
start_function.
forward_call (kfree_spec_sub KAF_APD t_run) (new_head, gv, sh , ls, xx, orig_head). (* call kfree *)
    + destruct (eq_dec new_head nullval).
        *unfold KAF_globals. entailer!.
        * unfold KAF_globals. entailer!. 
            simplify_kalloc_token. 
    + destruct (eq_dec new_head nullval).
        *forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head ). (* kalloc *)
        destruct (eq_dec orig_head nullval).
            --forward. Exists nullval. entailer!. unfold KAF_globals; entailer!.
            -- forward. Exists orig_head. entailer.
            Exists (fst ab) (snd ab). unfold type_kalloc_token. unfold KAF_globals. entailer!.
        * forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh, orig_head::ls, xx, new_head ). (* kalloc *)
        destruct (eq_dec new_head nullval).
            -- forward.
            -- forward. Exists new_head. entailer. inversion H0; subst; entailer. unfold KAF_globals. entailer!. simplify_kalloc_token.
Qed.

Lemma body_kfree_kalloc_inverses: semax_body KAFVprog KAFGprog f_kfree_kalloc kfree_kalloc_inverses_spec.
Proof.
start_function.
forward_call (kfree_spec_sub KAF_APD t_run) (new_head, gv, sh , ls, xx, orig_head). (* call kfree *)
    + if_tac_auto_contradict.
        *unfold KAF_globals. entailer!.
        * unfold KAF_globals. entailer!. 
            simplify_kalloc_token. 
    + if_tac_auto_contradict.
        *forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head ). (* kalloc *)
        if_tac; forward.
        *forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh, orig_head::ls, xx, new_head ). (* kalloc *)
        if_tac_auto_contradict; forward.
        inversion H2; subst; entailer. unfold KAF_globals. entailer!. simplify_kalloc_token.
Qed.

Lemma body_kalloc_kfree_inverses: semax_body KAFVprog KAFGprog f_kalloc_kfree kalloc_kfree_inverses_spec.
Proof.
start_function.
forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head).
- unfold KAF_globals. entailer!.
- if_tac.
    + forward_call (kfree_spec_sub KAF_APD t_run) (nullval, gv, sh , ls, xx, orig_head).
        * if_tac_auto_contradict. entailer!.
        * if_tac_auto_contradict. unfold KAF_globals. entailer!.
    + Intros ab. assert_PROP(isptr orig_head).
        * unfold type_kalloc_token. entailer!.
        * forward_call (kfree_spec_sub KAF_APD t_run) (orig_head, gv, sh , snd ab, xx, fst ab).
        -- if_tac_auto_contradict. entailer!.
        -- if_tac_auto_contradict. unfold KAF_globals. entailer!.
Qed.

Lemma body_kalloc_write_42_kfree: semax_body KAFVprog KAFGprog f_kalloc_write_42_kfree kalloc_write_42_kfree_spec.
Proof.
start_function.
Intros.
forward.
- forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, orig_head ). (* kalloc *)
+ unfold KAF_globals. entailer!.
+ if_tac_auto_contradict.
    * forward_if.
        -- rewrite H in H0; auto_contradict.
        -- forward. Exists (Vint(Int.repr 0)). entailer.
    * Intros ab.
    destruct ls; auto_contradict.
    forward_if.
      -- unfold type_kalloc_token. rewrite kalloc_token_sz_split.
      destruct orig_head eqn:eo; inversion H0; auto_contradict.
      assert_PROP (Ptrofs.unsigned i + PGSIZE < Ptrofs.modulus).
      {
      Intros. entailer!.
      }
      rewrite token_merge with (b:= b) (i:= i); auto.
      2: { try rep_lia. }
      Intros.
      assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as HH11. { try rep_lia. }
      rewrite <- HH11.
      destruct orig_head; auto_contradict.
      assert (i = Ptrofs.repr (Ptrofs.unsigned i)). { rewrite Ptrofs.repr_unsigned. auto. }
      rewrite H12 at 2.
      rewrite memory_block_split with (sh := sh) (n:=(sizeof tint)) (m :=(PGSIZE - sizeof tint)) (b := b); try rep_lia.
      rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
      rewrite <- H12.
      forward. forward.
      forward_call (kfree_spec_sub KAF_APD tint) (Vptr b i, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        ++ if_tac_auto_contradict.
            unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
            sep_apply data_at_memory_block. 
            rewrite token_merge with (b:= b) (i:= i); auto; try rep_lia.
            assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as Hpgsizetint; try rep_lia.
            rewrite <- Hpgsizetint at 2.
            rewrite H12 at 3.
            rewrite memory_block_split with (n := sizeof tint) (m:= PGSIZE - sizeof tint ); try rep_lia.
            rewrite <- H12.
            entailer!.
        ++ if_tac_auto_contradict.
            forward. Exists (Vint (Int.repr 42)). inversion H0. unfold KAF_globals. entailer.
        ++ rewrite <- H12. auto.
        -- forward.
Qed.


Lemma body_kalloc_write_40_2_kfree: semax_body KAFVprog KAFGprog f_kalloc_write_40_2_kfree kalloc_write_40_2_kfree_spec.
Proof.
start_function.
Intros.
repeat forward. 
forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, orig_head ). (* kalloc *)
+ unfold KAF_globals. entailer!.
+ if_tac_auto_contradict.
    * forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, orig_head). (* kalloc *)
        -- entailer!.
        -- if_tac_auto_contradict. Intros. forward.
            forward_if (
                PROP  ( )
                LOCAL ( temp _X (Vint (Int.repr 0)); temp _pa2 orig_head;
                        temp _pa1 orig_head; gvars gv )
                SEP ( EX r,
                    (!! (r = Vint (Int.repr 0)) &&
                    KAF_globals gv  sh ls xx orig_head) 
                )
            ).
            ++ rewrite H in H1; auto_contradict.
            ++ forward. Exists (Vint(Int.repr 0)). entailer.
            ++ forward_if (
                PROP  ( )
                LOCAL ( temp _X (Vint (Int.repr 0)); temp _pa2 orig_head;
                        temp _pa1 orig_head; gvars gv )
                SEP ( EX r,
                    (!! (r = Vint (Int.repr 0)) &&
                    KAF_globals gv  sh ls xx orig_head) 
                )
            ).
            ** rewrite H in H1; auto_contradict.
            ** forward. Exists (Vint(Int.repr 0)). entailer.
            ** forward. Exists (Vint(Int.repr 0)). entailer.
    * 
    Intros ab. forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , (snd ab), xx, (fst ab)). (* kalloc *)
        forward.
        if_tac_auto_contradict.
        -- Intros.
        forward_if (
            PROP  ( )
            LOCAL ( temp _X (Vint (Int.repr 0));
                    temp _pa1 orig_head; gvars gv )
            SEP ( 
                EX r,
                (!! ( r = Vint (Int.repr 0) ) &&
                (KAF_globals gv  sh (snd ab) xx (fst ab) * type_kalloc_token KAF_APD sh tint orig_head))
            )
        ).
            ++ rewrite H1; entailer!.
            ++ assert (isptr (fst ab)); auto. rewrite H1 in H3; auto_contradict.
            ++ forward. Exists (Vint (Int.repr 0)). unfold KAF_globals; entailer!.
            ++ Intros x.
            forward_if (
                PROP  ( )
                LOCAL ( temp _X (Vint (Int.repr 40));
                        gvars gv )
                SEP ( EX r,
                    (!! (r = Vint (Int.repr 40)) &&
                    KAF_globals gv  sh ls xx orig_head) 
                )
            ).
        ---
        unfold type_kalloc_token. rewrite kalloc_token_sz_split. 
      destruct orig_head eqn:eo; inversion H0; auto_contradict.
      assert_PROP (Ptrofs.unsigned i + PGSIZE < Ptrofs.modulus). { Intros. entailer!. }
      rewrite token_merge with (b:= b) (i:= i); auto.
      2: { try rep_lia. }
      Intros.
      assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as HH11. { try rep_lia. }
      rewrite <- HH11.
      destruct orig_head; auto_contradict.
      assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH12. { rewrite Ptrofs.repr_unsigned. auto. }
      rewrite HH12 at 2.
      rewrite memory_block_split with (sh := sh) (n:=(sizeof tint)) (m :=(PGSIZE - sizeof tint)) (b := b); try rep_lia.
      rewrite <- HH12.
      rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
      forward. forward. forward.
      forward_call (kfree_spec_sub KAF_APD tint) (Vptr b i, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        ** if_tac_auto_contradict.
            unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer.
            sep_apply data_at_memory_block.
            unfold KAF_globals.
            entailer!.
            rewrite token_merge with (b:= b) (i:= i) (p := Vptr b i); auto; try rep_lia.
            assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as Hpgsizetint; try rep_lia.
            rewrite <- Hpgsizetint at 2.
            rewrite HH12 at 3.
            rewrite memory_block_split with (n := sizeof tint) (m:= PGSIZE - sizeof tint ); try rep_lia.
            rewrite <- HH12.
            entailer!.
        ** if_tac_auto_contradict. Exists (Vint (Int.repr 40)). 
            entailer.
        --- forward. Exists (Vint (Int.repr 40)). entailer.
        --- forward. Exists (Vint (Int.repr 40)). unfold KAF_globals. rewrite mem_mgr_split at 1.
        refold_freelistrep.
        destruct (snd ab) eqn:e2; auto_contradict.
        2: { entailer!. refold_freelistrep. rewrite H1. entailer!. }
        destruct ((1 <? Datatypes.length [fst ab])%nat) eqn:e1; auto_contradict.
        rewrite mem_mgr_split.
        entailer.
        refold_freelistrep. entailer!.
    -- forward_if (
            PROP  ( )
            LOCAL ( temp _X (Vint (Int.repr 2)); temp _pa2 (fst ab);
                    temp _pa1 orig_head; gvars gv)
            SEP ( EX r,
                (!! ( r = Vint (Int.repr 2) ) &&
                KAF_globals gv  sh (snd ab) xx (fst ab) * kalloc_token_sz sh (sizeof tint) (orig_head))
            )
        ).
        ++ Intros ab0. 
        unfold type_kalloc_token. rewrite kalloc_token_sz_split.
        assert_PROP(isptr (fst ab)). { entailer. }
      destruct (fst ab) eqn:efab; inversion H0; auto_contradict.
      assert_PROP (Ptrofs.unsigned i + PGSIZE < Ptrofs.modulus). { Intros. entailer. }
      rewrite token_merge with (b:= b) (i:= i); auto.
      2: { try rep_lia. }
      Intros.
      assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as HH11. { try rep_lia. }
      rewrite <- HH11.
      assert (isptr orig_head); unfold pointer_within_size_range in H9. auto.
      destruct orig_head; auto_contradict.
      assert (i = Ptrofs.repr (Ptrofs.unsigned i)) as HH12. { rewrite Ptrofs.repr_unsigned. auto. }
      rewrite HH12 at 2.
      rewrite memory_block_split with (sh := sh) (n:=(sizeof tint)) (m :=(PGSIZE - sizeof tint)) (b := b); try rep_lia.
      rewrite <- HH12.
      rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
      forward. forward.
      forward_call (kfree_spec_sub KAF_APD tint) (Vptr b i, gv, sh , snd ab0, xx, (fst ab0)). (* call kfree *)
        ** if_tac_auto_contradict.
            (*unfold type_kalloc_token.*)
            (*entailer!. rewrite kalloc_token_sz_split at 2. rewrite kalloc_token_sz_split. entailer.*)
            sep_apply data_at_memory_block.
            entailer!.
            assert ((Vptr b (Ptrofs.repr (Ptrofs.unsigned i + sizeof tint))) = offset_val (sizeof tint) (Vptr b i)) as HH0. {
                unfold offset_val.
                simpl. rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; auto; try rep_lia.
            }
            rewrite HH0.
            rewrite token_merge_size with (p := Vptr b i) (b:=b) (i:=i) (sz := sizeof tint); auto; try rep_lia.
            unfold type_kalloc_token.
            rewrite kalloc_token_sz_split. rewrite kalloc_token_sz_split.  
            rewrite token_merge with (p := Vptr b i) (b:=b) (i:=i); auto; try rep_lia.
            rewrite <- kalloc_token_sz_split.
            entailer!.
        ** if_tac_auto_contradict.
           Exists (Vint (Int.repr 2)). entailer.
           rewrite <- H3. unfold KAF_globals. entailer.
        ++ forward. Intros ab0. Exists (Vint (Int.repr 2)). entailer.
        ++
        assert_PROP (isptr orig_head). {
            rewrite kalloc_token_sz_split. 
            unfold pointer_within_size_range. Intros r.
            entailer!.
        } destruct ls; auto_contradict. 
        assert_PROP (isptr (fst ab)). { unfold KAF_globals. rewrite mem_mgr_split. Intros r. destruct H6; destruct H6. rewrite H7 in H1. auto_contradict. entailer!. }
        Intros r. rewrite kalloc_token_sz_split. 
        destruct (eq_dec orig_head nullval)  eqn:e1; auto_contradict.
        forward_if ( orig_head <> nullval ).
         forward_if (
            PROP  ( )
            LOCAL ( temp _X (Vint (Int.repr 42)); temp _pa2 (fst ab);
                    temp _pa1 orig_head; gvars gv)
            SEP ( EX r,
                (!! ( r = Vint (Int.repr 42) ) &&
                KAF_globals gv  sh ls xx orig_head)
            )
        ).
        **
        entailer!.




            rewrite token_merge with (b:= b0) (i:= i0) (p := Vptr b0 i0); auto; try rep_lia.

            
            rewrite <- token_merge_size with (p := Vptr b0 i0) (b:=b0) (i:=i0) (sz := sizeof tint); auto; try rep_lia.
            entailer!.

            


            assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as Hpgsizetint; try rep_lia.
            rewrite <- Hpgsizetint at 2.

            rewrite HH12 at 1. 
            rewrite memory_block_split with (n := sizeof tint) (m:= PGSIZE - sizeof tint ); try rep_lia.
            rewrite <- HH12.
            entailer!.
        ** if_tac_auto_contradict. Exists (Vint (Int.repr 40)). 
            entailer.
        --- forward. Exists (Vint (Int.repr 40)). entailer!.
        --- forward. Exists (Vint (Int.repr 40)). unfold KAF_globals. rewrite mem_mgr_split at 1.
        refold_freelistrep.
        destruct (snd ab) eqn:e2; auto_contradict.
        2: { entailer!. refold_freelistrep. rewrite H1. entailer!. }
        destruct ((1 <? Datatypes.length [fst ab])%nat) eqn:e1; auto_contradict.
        rewrite mem_mgr_split.
        entailer!.
        refold_freelistrep. entailer!.
        








            
            inversion H0. unfold KAF_globals. entailer.
        ++ rewrite <- H12. auto.
        -- forward.
Qed.
        
Lemma body_kfree_kalloc_twice: semax_body KAFVprog KAFGprog_clients f_kfree_kalloc_twice kfree_kalloc_twice_spec.
Proof.
start_function. destruct H.
forward_call (gv, sh, pa1, orig_head, xx, ls).
- entailer!.
- Intros vret.
    if_tac.
    + if_tac.
        * if_tac.
            -- forward_call (gv, sh, pa2, orig_head, xx, ls).
                ++ if_tac_auto_contradict.
                    entailer!.
                ++ if_tac_auto_contradict. Intros vret0.
                    if_tac_auto_contradict.
                    forward.
                    Exists vret0. entailer!.
                    destruct H6 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto.
            --forward_call (gv, sh, pa2, orig_head, xx, ls).
                ++ if_tac_auto_contradict. entailer!.
                ++ if_tac_auto_contradict. Intros vret0. forward.
                    Exists vret0. entailer!.
                    destruct H6 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict. do 4 right. left. auto.
        * if_tac; Intros ab.
            -- destruct ls as [ | next1 ls1]; auto_contradict. (*unfold abbreviate in POSTCONDITION.*)
                forward_call (gv, sh, pa2, next1, xx, ls1).
                ++ if_tac_auto_contradict.
                inversion H5. rewrite H8; rewrite H9. entailer!.
                ++ if_tac_auto_contradict. if_tac_auto_contradict. 
                    ** Intros vret0. forward.
                    Exists vret0. Exists nullval ls1. if_tac_auto_contradict. entailer!.
                    destruct H8 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict. 
                    do 5 right. split; auto.
                    ** Intros vret0. Intros ab0. forward.
                    Exists vret0. Exists (next1) (snd ab). if_tac_auto_contradict.
                    Exists (fst ab0) (snd ab0). entailer!.
                    do 5 right. split; auto.
            -- destruct ls as [ | next1 ls1]; auto_contradict. 
                forward_call (gv, sh, pa2, next1, xx, ls1).
                ++ if_tac_auto_contradict.
                inversion H5. rewrite H8; rewrite H9. entailer!.
                ++ Intros vret0. forward. if_tac_auto_contradict.
                Exists vret0. Exists next1 ls1. entailer!.
                destruct H6 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict. 
                do 4 right. left; split; auto.
    + if_tac.
        -- forward_call (gv, sh, pa2, orig_head, xx, ls).
            ++ if_tac_auto_contradict.
                entailer!.
            ++ if_tac_auto_contradict. Intros vret0.
                if_tac_auto_contradict.
                ** forward. 
                Exists vret0. entailer!.
                destruct H5 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto.
                do 2 right. left. split; auto.
                ** Intros ab.
                    forward. Exists vret0. Exists (fst ab) (snd ab). entailer!.
                    destruct H5 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto.
                    do 2 right. left; split; auto.
                    do 3 right. left; split; auto.
        -- Intros. forward_call (gv, sh, pa2, orig_head, xx, ls).
            ++ if_tac_auto_contradict. entailer!.
            ++ if_tac_auto_contradict. 
                Intros vret0. forward.
                Exists vret0. entailer!.
                destruct H5 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict.
                ** right. left; split; auto.
Qed.
        
        
Lemma body_kfree_kalloc_kfree_kalloc: semax_body KAFVprog KAFGprog f_kfree_kalloc_kfree_kalloc kfree_kalloc_kfree_kalloc_spec.
Proof.
start_function. Intros.
if_tac; if_tac; destruct H; 
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- if_tac_auto_contradict. unfold KAF_globals. entailer!.
- forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc *)
    + if_tac_auto_contradict. entailer!.
    + if_tac_auto_contradict. 
        * forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx, orig_head). (* call kfree *)
            -- if_tac_auto_contradict. entailer!.
            -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc *)
                if_tac.
                    ++ forward. Exists nullval; unfold KAF_globals. entailer!.
                    ++ Intros ab. destruct ls; auto_contradict.
        * Intros ab. destruct ls; auto_contradict. 
        forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
            -- entailer!.
            -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , snd ab, xx, fst ab). (* kalloc *)
                if_tac.
                    ++ forward. Exists (fst ab) (fst ab) (snd ab). if_tac.
                        ** unfold KAF_globals. unfold type_kalloc_token. entailer!. repeat right. split; auto.
                        ** entailer.
                    ++ Intros ab0. forward. Exists (fst ab). unfold type_kalloc_token. rewrite mem_mgr_split. 
                        Exists (fst ab) (snd ab). if_tac_auto_contradict. Exists (fst ab0) (snd ab0). rewrite mem_mgr_split; entailer!.
                        repeat right; split; auto.
-if_tac_auto_contradict. unfold KAF_globals. entailer!.
- forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc *)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. 
    * forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx, orig_head). (* call kfree *)
        -- if_tac_auto_contradict. unfold type_kalloc_token. entailer!.
        -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , (orig_head :: ls), xx, pa2). (* kalloc *)
            if_tac.
                ++ forward.
                ++ Intros ab. destruct ls; auto_contradict;
                    forward; unfold type_kalloc_token, KAF_globals; inversion H6; rewrite H3; rewrite H9; Exists pa2; entailer!;
                    do 4 right; left; split; auto.
    * Intros ab. destruct ls; auto_contradict.  
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
        -- if_tac_auto_contradict. unfold type_kalloc_token at 2. rewrite kalloc_token_sz_split. entailer!.
        -- if_tac_auto_contradict. rewrite mem_mgr_split. Intros. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
            ++ unfold type_kalloc_token. rewrite mem_mgr_split.  entailer!.
            ++ forward. if_tac_auto_contradict. Intros ab0. Exists pa2 (fst ab0) (snd ab0). rewrite mem_mgr_split. unfold KAF_globals, type_kalloc_token. rewrite mem_mgr_split. entailer!.
                do 4 right. left; split; auto.
- if_tac_auto_contradict. unfold KAF_globals. rewrite kalloc_token_sz_split. unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
- if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    ++ entailer!.
    ++ if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , snd ab, xx, fst ab). (* kalloc *)
        forward. if_tac_auto_contradict; inversion H5.
        ** Exists (fst ab). if_tac_auto_contradict.
        unfold type_kalloc_token, KAF_globals. entailer!.
        do 2 right; left; split; auto.
        ** Intros ab0. Exists (fst ab). if_tac_auto_contradict.
            Exists (fst ab0) (snd ab0). unfold type_kalloc_token, KAF_globals. entailer!.
            do 3 right; left; split; auto.
- if_tac_auto_contradict. unfold KAF_globals. unfold type_kalloc_token. entailer!.
- if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    + if_tac_auto_contradict. unfold type_kalloc_token at 2; entailer!.
    + if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab0. forward. Exists pa2. unfold KAF_globals. unfold type_kalloc_token; entailer!.
    inversion H8. rewrite H14, H15. inversion H5. entailer!.
        Qed.
        
Lemma body_kfree_kfree_kalloc: semax_body KAFVprog KAFGprog f_kfree_kfree_kalloc kfree_kfree_kalloc_spec.
Proof.
start_function.
Intros.
if_tac; if_tac; destruct H; 
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- if_tac_auto_contradict. unfold KAF_globals. entailer!.
- if_tac_auto_contradict;
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx, orig_head). (* call kfree*)
    + if_tac_auto_contradict. entailer!.
    + if_tac_auto_contradict.
        forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, orig_head). (* kalloc *)
        if_tac_auto_contradict. 
        * forward. Exists nullval. unfold KAF_globals. entailer!.
        * forward. Exists orig_head. Exists (fst ab) (snd ab). entailer!. 
        unfold type_kalloc_token, KAF_globals. entailer!.
-if_tac_auto_contradict. unfold KAF_globals. entailer!.
-if_tac_auto_contradict;
forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , ls, xx,orig_head). (* call kfree*)
+ if_tac_auto_contradict. entailer!. unfold type_kalloc_token; entailer!. 
+ if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. 
    forward. Exists pa2. unfold KAF_globals. entailer!.
        * do 3 right. split; auto.
        * unfold type_kalloc_token. entailer!. inversion H0. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold KAF_globals, type_kalloc_token. entailer!.
- if_tac_auto_contradict. 
forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , orig_head::ls, xx,pa1). (* call kfree*)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab. forward. Exists pa1. unfold type_kalloc_token, KAF_globals. entailer!.
    * do 2 right; left; split; auto.
    * inversion H6. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold type_kalloc_token, KAF_globals. entailer!.
- if_tac_auto_contradict. forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , orig_head::ls, xx,pa1). (* call kfree*)
    + if_tac_auto_contradict. unfold type_kalloc_token. entailer!.
    + if_tac_auto_contradict. forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , pa1::orig_head::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. Intros ab.
    forward. Exists pa2. unfold KAF_globals, type_kalloc_token. entailer!.
    inversion H6.
    entailer.
Qed.
        

Lemma body_kalloc_write_42_kfree_kfree: semax_body KAFVprog KAFGprog f_kalloc_write_42_kfree_kfree kalloc_write_42_kfree_kfree_spec.
Proof.
start_function.
Intros.
forward.
- forward_call (kalloc_spec_sub KAF_APD tint) (gv, sh , ls, xx, orig_head ). (* kalloc *)
+ unfold KAF_globals. entailer!.
+ if_tac_auto_contradict.
    * forward_if.
        -- rewrite H in H0; auto_contradict.
        -- forward_call (kfree_spec_sub KAF_APD t_run) (orig_head, gv, sh , ls, xx,orig_head). (* call kfree*)
        ++ if_tac_auto_contradict. entailer!.
        ++ rewrite H. simpl. auto.
        ++ if_tac_auto_contradict. 
        forward. Exists (Vint(Int.repr 0)). entailer.
    * Intros ab.
    destruct ls; auto_contradict.
    forward_if.
      -- unfold type_kalloc_token. rewrite kalloc_token_sz_split.
      destruct orig_head eqn:eo; inversion H0; auto_contradict.
      assert_PROP (Ptrofs.unsigned i + PGSIZE < Ptrofs.modulus).
      {
      Intros. entailer!.
      }
      rewrite token_merge with (b:= b) (i:= i); auto.
      2: { try rep_lia. }
      Intros.
      assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as HH11. { try rep_lia. }
      rewrite <- HH11.
      destruct orig_head; auto_contradict.
      assert (i = Ptrofs.repr (Ptrofs.unsigned i)). { rewrite Ptrofs.repr_unsigned. auto. }
      rewrite H12 at 2.
      rewrite memory_block_split with (sh := sh) (n:=(sizeof tint)) (m :=(PGSIZE - sizeof tint)) (b := b); try rep_lia.
      rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros.
      rewrite <- H12.
      forward. forward.
      forward_call (kfree_spec_sub KAF_APD tint) (Vptr b i, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        ++ if_tac_auto_contradict.
            unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
            sep_apply data_at_memory_block. 
            rewrite token_merge with (b:= b) (i:= i); auto; try rep_lia.
            assert (sizeof tint + (PGSIZE - sizeof tint) = PGSIZE) as Hpgsizetint; try rep_lia.
            rewrite <- Hpgsizetint at 2.
            rewrite H12 at 3.
            rewrite memory_block_split with (n := sizeof tint) (m:= PGSIZE - sizeof tint ); try rep_lia.
            rewrite <- H12.
            entailer!.
        ++ if_tac_auto_contradict.
            forward. Exists (Vint (Int.repr 42)). inversion H0. unfold KAF_globals. entailer.
        ++ rewrite <- H12. auto.
        --  forward_call (kfree_spec_sub KAF_APD tint) (orig_head, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        ++ if_tac_auto_contradict.
            (*unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
            sep_apply data_at_memory_block. entailer!.*)
        ++ if_tac_auto_contradict. 
        Unshelve. rewrite H1 in H. auto_contradict.
Qed.


Lemma body_kfree_kfree_kalloc_kalloc: semax_body KAFVprog KAFGprog f_kfree_kfree_kalloc_kalloc kfree_kfree_kalloc_kalloc_spec.
Proof.
start_function.
Intros.
destruct H. 
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- unfold KAF_globals.
    if_tac.
    + rewrite H1 in H. auto_contradict.
    + unfold type_kalloc_token. entailer!. 
- if_tac_auto_contradict. rewrite H1 in H. auto_contradict.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa2, gv, sh , orig_head::ls, xx, pa1).
    if_tac_auto_contradict. rewrite H2 in H0; auto_contradict.
    unfold type_kalloc_token.
    entailer!.
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , pa1::orig_head::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict; entailer!.
    if_tac_auto_contradict. rewrite H2 in H0; auto_contradict.
    Intros ab. 
    forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , orig_head::ls, xx, pa1). (* kalloc *)
    inversion H3. entailer!.
    if_tac_auto_contradict.
    Intros ab0. 
    forward. unfold type_kalloc_token. entailer!. unfold KAF_globals. inversion H5; entailer.
Qed.

Lemma body_kfree_kfree_same_wrong_pointer: semax_body KAFVprog KAFGprog f_kfree_kfree_same_pointer kfree_kfree_same_pointer_wrong_spec.
Proof.
start_function.
Intros.
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, orig_head). (* call kfree *)
- unfold KAF_globals.
    if_tac.
    + rewrite H0 in H. auto_contradict.
    + unfold type_kalloc_token. entailer!. 
- if_tac_auto_contradict. rewrite H0 in H. auto_contradict.
    forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , orig_head::ls, xx, pa1).
    +  if_tac_auto_contradict. (*rewrite H2 in H0; auto_contradict.*)
    unfold type_kalloc_token.
    entailer!.
    + if_tac_auto_contradict.
      entailer. 
Qed.