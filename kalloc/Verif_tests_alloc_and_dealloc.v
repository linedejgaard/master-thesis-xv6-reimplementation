Require Import VST.floyd.proofauto.


Require Import VC.ASI_kalloc.
Require Import VC.kallocfun.
Require Import VC.Spec_kalloc.
Require Import VC.clientsfun.
Require Import VC.tactics.

Require Import VC.kalloc.

Local Open Scope logic.


Definition kfree_kalloc_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, original_freelist_pointer:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(is_pointer_or_null new_head /\
            (~ In new_head (original_freelist_pointer::ls) \/ new_head = nullval)
        ) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KAF_globals gv sh ls xx original_freelist_pointer *
            (if eq_dec new_head nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) new_head))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP( 
            ((new_head = nullval) /\ ( original_freelist_pointer = nullval) /\ r = nullval) \/
            ((new_head <> nullval) /\  r = new_head) \/
            ((new_head = nullval) /\ ( original_freelist_pointer <> nullval) /\ r = original_freelist_pointer)
        )
        RETURN (r) (* we return the head like in the pop function*)
        SEP (
            let freelist_case :=
            if eq_dec original_freelist_pointer nullval then
            emp * KAF_globals gv sh ls xx original_freelist_pointer
            else
            EX next, EX ls',
                !! (next :: ls' = ls) &&
                KAF_globals gv sh ls' xx next *
                kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer
        in
        
        let newhead_case :=
            KAF_globals gv sh ls xx original_freelist_pointer *
            kalloc_token' KAF_APD sh (sizeof t_run) new_head
        in
        
        if eq_dec new_head nullval then
            freelist_case
        else
            newhead_case
).

Definition kalloc_write_42_kfree_spec : ident * funspec :=
    DECLARE _kalloc_write_42_kfree
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx original_freelist_pointer)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec original_freelist_pointer nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx original_freelist_pointer)
            else
                (!! ( r = Vint (Int.repr 42) ) &&
                KAF_globals gv  sh ls xx original_freelist_pointer)
            )
        ).
        
Definition kfree_kalloc_twice_spec:= 
    DECLARE _kfree_kalloc_twice
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls:list val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2 /\
            (~ In pa1 (original_freelist_pointer::ls) \/ pa1 = nullval) /\
            (~ In pa2 (original_freelist_pointer::ls)  \/ pa2 = nullval) /\
            ~ (pa1 = pa2)
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx original_freelist_pointer *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( original_freelist_pointer = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (original_freelist_pointer = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (original_freelist_pointer <> nullval) /\ (r = original_freelist_pointer)) \/ (* then there is exists a value or null in ls that is returned *)
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( original_freelist_pointer <> nullval)) (* r is either nullval or next next*)
            ) 
            RETURN (r) (* we return the head like in the pop function*)
            SEP 
            (
                let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                (if eq_dec original_freelist_pointer nullval then
                    KAF_globals gv sh ls xx original_freelist_pointer * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec original_freelist_pointer nullval then 
                        KAF_globals gv sh ls xx original_freelist_pointer * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KAF_globals gv sh ls' xx next *
                        kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec original_freelist_pointer nullval then
                        emp * KAF_globals gv sh ls xx original_freelist_pointer
                    else
                        (kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer *
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
                KAF_globals gv sh ls xx original_freelist_pointer *
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
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls:list val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2 /\
            (~ In pa1 (original_freelist_pointer::ls) \/ pa1 = nullval) /\
            (~ In pa2 (original_freelist_pointer::ls)  \/ pa2 = nullval) /\
            ~ (pa1 = pa2)
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx original_freelist_pointer *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( original_freelist_pointer = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (original_freelist_pointer = nullval) /\ r = nullval) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ (original_freelist_pointer <> nullval) /\ (r = original_freelist_pointer)) \/ (* then there is exists a value or null in ls that is returned *)
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 = nullval) /\ (pa2 = nullval) /\ ( original_freelist_pointer <> nullval)) (* r is either nullval or next next*)
            ) 
            RETURN (r) (* we return the head like in the pop function*)
            SEP 
            (
                let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                (if eq_dec original_freelist_pointer nullval then
                    KAF_globals gv sh ls xx original_freelist_pointer * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec original_freelist_pointer nullval then 
                        KAF_globals gv sh ls xx original_freelist_pointer * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KAF_globals gv sh ls' xx next *
                        kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec original_freelist_pointer nullval then
                        emp * KAF_globals gv sh ls xx original_freelist_pointer
                    else
                        (kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer *
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
                KAF_globals gv sh ls xx original_freelist_pointer *
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
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2 /\
            (~ In pa1 (original_freelist_pointer::ls) \/ pa1 = nullval) /\
            (~ In pa2 (original_freelist_pointer::ls)  \/ pa2 = nullval) /\
            ~ (pa1 = pa2)
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx original_freelist_pointer *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KAF_APD sh (sizeof t_run) pa2))
        )
    POST [ tptr tvoid ]
        EX r,
        PROP(
            ((pa1 = nullval) /\ (pa2 = nullval) /\ r = original_freelist_pointer) \/
            ((pa1 <> nullval) /\  (pa2 <> nullval) /\ r = pa2) \/
            ((pa1 <> nullval) /\  (pa2 = nullval) /\ r = pa1) \/
            ((pa1 = nullval) /\  (pa2 <> nullval) /\ r = pa2)
        )
        RETURN (r) (* we return the head like in the pop function*)
        SEP 
        (
            let freelist_only_pa1_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa2 *
                KAF_globals gv sh ls xx original_freelist_pointer
            in
            let freelist_only_pa2_null_case :=
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 * 
                KAF_globals gv sh ls xx original_freelist_pointer
            in
            let freelist_both_null_case :=
                if eq_dec original_freelist_pointer nullval then
                    emp * KAF_globals gv sh ls xx original_freelist_pointer
                else
                    (EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KAF_globals gv sh ls' xx next *
                    kalloc_token' KAF_APD sh (sizeof t_run) original_freelist_pointer)
            in
            let both_is_pointers_case :=
                KAF_globals gv sh (original_freelist_pointer::ls) xx pa1 *
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
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx original_freelist_pointer)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec original_freelist_pointer nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KAF_globals gv  sh ls xx original_freelist_pointer)
            else
                (!! ( r = Vint (Int.repr 42) ) &&
                KAF_globals gv  sh ls xx original_freelist_pointer)
            )
        ).

Definition kfree_kfree_kalloc_kalloc_spec := 
    DECLARE _kfree_kfree_kalloc_kalloc
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            isptr pa1 /\
            isptr pa2 /\
            (~ In pa1 (original_freelist_pointer::ls) \/ pa1 = nullval) /\
            (~ In pa2 (original_freelist_pointer::ls)  \/ pa2 = nullval) /\
            ~ (pa1 = pa2)
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx original_freelist_pointer *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
            kalloc_token' KAF_APD sh (sizeof t_run) pa2
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (pa1) (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv  sh ls xx original_freelist_pointer *
                kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KAF_APD sh (sizeof t_run) pa2
                ).

Definition kfree_kfree_same_pointer_wrong_spec := 
    DECLARE _kfree_kfree_same_pointer
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            isptr pa1 /\
            (~ In pa1 (original_freelist_pointer::ls) \/ pa1 = nullval) 
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            KAF_globals gv  sh ls xx original_freelist_pointer *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1 *
            kalloc_token' KAF_APD sh (sizeof t_run) pa1
            )
    POST [ tvoid ]
        PROP( )
            RETURN () (* we return the head like in the pop function*)
            SEP 
            (
                KAF_globals gv  sh (pa1::original_freelist_pointer::ls) xx pa1
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
forward_call (kfree_spec_sub KAF_APD t_run) (new_head, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
    + destruct (eq_dec new_head nullval).
        *unfold KAF_globals. entailer!.
        * unfold KAF_globals. entailer!. 
            simplify_kalloc_token. 
    + destruct (eq_dec new_head nullval).
        *forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
        destruct (eq_dec original_freelist_pointer nullval).
            -- forward. Exists nullval. unfold KAF_globals. entailer!.
            -- destruct ls.
                ++ forward. auto_contradict.
                ++ forward. Exists original_freelist_pointer. entailer. Exists v. entailer.
                    Exists ls. entailer. unfold KAF_globals. entailer!. inversion H0; subst. entailer!.
                    simplify_kalloc_token. 
        *forward_call (kalloc_spec_sub KAF_APD t_run) (gv, sh, original_freelist_pointer::ls, xx, new_head). (* kalloc *)
        destruct (eq_dec new_head nullval).
            -- forward.
            -- forward. Exists new_head. entailer. inversion H0; subst; entailer. unfold KAF_globals. entailer!. simplify_kalloc_token.
Qed.

Lemma body_kfree_kfree_same_wrong_pointer: semax_body KAFVprog KAFGprog f_kfree_kfree_same_pointer kfree_kfree_same_pointer_wrong_spec.
Proof.
start_function.
Intros.
forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
- unfold KAF_globals.
    if_tac.
    + rewrite H0 in H. destruct H. auto_contradict.
    + unfold type_kalloc_token. entailer!. 
- split; destruct H. unfold is_pointer_or_null. destruct pa1; auto_contradict; auto.
destruct H0. left; auto. right; auto.
- if_tac_auto_contradict.
    + rewrite H0 in H. auto_contradict. forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , original_freelist_pointer::ls, xx, pa1).
    * if_tac_auto_contradict. (*rewrite H2 in H0; auto_contradict.*)
    unfold type_kalloc_token.
    entailer!.
    * destruct H. auto_contradict.
    * if_tac_auto_contradict.
      entailer. unfold KAF_globals. rewrite mem_mgr_split. rewrite mem_mgr_split.
      entailer!.
      -- destruct H3. 
        ++ destruct H3; auto_contradict.
        ++  destruct H; auto_contradict.
      -- destruct H; auto_contradict.
    + forward_call (kfree_spec_sub KAF_APD t_run) (pa1, gv, sh , original_freelist_pointer::ls, xx, pa1).
    * if_tac_auto_contradict. unfold type_kalloc_token. entailer!.
    * destruct H as [H [H1 | H2]]. 
        -- split. destruct pa1; auto_contradict; unfold is_pointer_or_null; auto.
        assert (exists ls : list val, In pa1 (original_freelist_pointer :: ls)). 
        {
            exists [pa1].
            simpl. right. left. auto.
        }
           left. intros HH. apply H1.
           (* we have that 
            ~ In pa1 (original_freelist_pointer :: ls) and
            exists ls : list val, In pa1 (original_freelist_pointer :: ls)
            *)
Abort.