Require Import VST.floyd.proofauto.

Require Import VC.ASI_kalloc.
Require Import VC.kalloc_kfree_definitions.
Require Import VC.Spec_kalloc.
Require Import VC.kallocfun.
Require Import VC.clientsfun.
Require Import VC.tactics.

Require Import VC.kalloc.


#[export] Instance CompSpecs : compspecs. make_compspecs kalloc.prog. Defined. (* this is my problem.. *)

Local Open Scope logic.

Definition KF_ASI: funspecs := Kalloc_ASI KF_APD _kalloc _kfree.
Definition KF_imported_specs:funspecs := nil.
Definition KF_internal_specs: funspecs := KF_ASI.
Definition KF_globals gv  sh ls xx original_freelist_pointer: mpred:= ASI_kalloc.mem_mgr KF_APD gv sh ls xx original_freelist_pointer.
Definition KFVprog : varspecs. mk_varspecs kalloc.prog. Defined.
Definition KFGprog: funspecs := KF_imported_specs ++ KF_internal_specs.

Definition kalloc_write_pipe_spec : ident * funspec :=
 DECLARE _kalloc_write_pipe
 WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
 PRE [ ] 
    PROP () PARAMS() GLOBALS(gv) SEP (KF_globals gv sh ls xx original_freelist_pointer)
 POST [ tvoid ] 
    PROP ( ) RETURN () SEP (
        (if eq_dec original_freelist_pointer nullval then
            KF_globals gv  sh ls xx original_freelist_pointer *emp
        else
        EX next ls',
          (!! (next :: ls' = ls) &&
                pipe_rep sh original_freelist_pointer *
                KF_globals gv  sh ls' xx next
        )
        )
    ).
    
Definition kfree_kalloc_spec := 
    DECLARE _kfree_kalloc
    WITH gv:globals, sh : share, new_head:val, original_freelist_pointer:val, xx:Z, ls:list val
    PRE [ tptr tvoid ]
        PROP(is_pointer_or_null new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            KF_globals gv  sh ls xx original_freelist_pointer *
            (if eq_dec new_head nullval then emp
            else (kalloc_token' KF_APD sh (sizeof t_run) new_head))
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
            emp * KF_globals gv sh ls xx original_freelist_pointer
            else
            EX next, EX ls',
                !! (next :: ls' = ls) &&
                KF_globals gv sh ls' xx next *
                kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer
        in
        
        let newhead_case :=
            KF_globals gv sh ls xx original_freelist_pointer *
            kalloc_token' KF_APD sh (sizeof t_run) new_head
        in
        
        if eq_dec new_head nullval then
            freelist_case
        else
            newhead_case
      
            ).

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

Definition kalloc_write_42_kfree_spec : ident * funspec :=
    DECLARE _kalloc_write_42_kfree
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (KF_globals gv sh ls xx original_freelist_pointer)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec original_freelist_pointer nullval then
                (!! (r = Vint (Int.repr 0)) &&
                KF_globals gv  sh ls xx original_freelist_pointer)
            else
                (!! ( r = Vint (Int.repr 42) ) &&
                KF_globals gv  sh ls xx original_freelist_pointer)
            )
        ).
        
Definition kfree_kalloc_twice_spec:= 
    DECLARE _kfree_kalloc_twice
    WITH sh : share, pa1:val, pa2:val, original_freelist_pointer:val, xx:Z, gv:globals, ls:list val
    PRE [ tptr tvoid, tptr tvoid ]
        PROP(
            is_pointer_or_null pa1 /\
            is_pointer_or_null pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KF_globals gv  sh ls xx original_freelist_pointer *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KF_APD sh (sizeof t_run) pa2))
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
                kalloc_token' KF_APD sh (sizeof t_run) pa2 *
                (if eq_dec original_freelist_pointer nullval then
                    KF_globals gv sh ls xx original_freelist_pointer * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KF_globals gv sh ls' xx next *
                    kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec original_freelist_pointer nullval then 
                        KF_globals gv sh ls xx original_freelist_pointer * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KF_globals gv sh ls' xx next *
                        kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec original_freelist_pointer nullval then
                        emp * KF_globals gv sh ls xx original_freelist_pointer
                    else
                        (kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer *
                        (EX next1, EX ls1,
                        !! (next1:: ls1 = ls) &&
                        if eq_dec next1 nullval then
                            KF_globals gv sh ls1 xx next1
                        else (
                        EX next2, EX ls2,
                        !! (next2:: ls2 = ls1) &&
                        KF_globals gv sh ls2 xx next2 * 
                        kalloc_token' KF_APD sh (sizeof t_run) next1
                        )))
                in
                let both_pointers_case :=
                KF_globals gv sh ls xx original_freelist_pointer *
                kalloc_token' KF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KF_APD sh (sizeof t_run) pa2
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
            is_pointer_or_null pa2
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KF_globals gv  sh ls xx original_freelist_pointer *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KF_APD sh (sizeof t_run) pa2))
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
                kalloc_token' KF_APD sh (sizeof t_run) pa2 *
                (if eq_dec original_freelist_pointer nullval then
                    KF_globals gv sh ls xx original_freelist_pointer * emp
                else
                    EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KF_globals gv sh ls' xx next *
                    kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer)
                in
                let freelist_only_pa2_null_case :=
                    kalloc_token' KF_APD sh (sizeof t_run) pa1 * 
                    (if eq_dec original_freelist_pointer nullval then 
                        KF_globals gv sh ls xx original_freelist_pointer * emp
                    else 
                        (EX next, EX ls',
                        !! (next :: ls' = ls) &&
                        KF_globals gv sh ls' xx next *
                        kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer) ) 
                in
                let freelist_both_null_case :=
                    if eq_dec original_freelist_pointer nullval then
                        emp * KF_globals gv sh ls xx original_freelist_pointer
                    else
                        (kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer *
                        (EX next1, EX ls1,
                        !! (next1:: ls1 = ls) &&
                        if eq_dec next1 nullval then
                            KF_globals gv sh ls1 xx next1
                        else (
                        EX next2, EX ls2,
                        !! (next2:: ls2 = ls1) &&
                        KF_globals gv sh ls2 xx next2 * 
                        kalloc_token' KF_APD sh (sizeof t_run) next1
                        )))
                in
                let both_pointers_case :=
                KF_globals gv sh ls xx original_freelist_pointer *
                kalloc_token' KF_APD sh (sizeof t_run) pa1 *
                kalloc_token' KF_APD sh (sizeof t_run) pa2
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
            is_pointer_or_null pa2 
        ) 
        PARAMS (pa1; pa2) GLOBALS(gv)
        SEP (
            KF_globals gv  sh ls xx original_freelist_pointer *
            (if eq_dec pa1 nullval then emp
            else (kalloc_token' KF_APD sh (sizeof t_run) pa1)) *
            (if eq_dec pa2 nullval then emp
            else (kalloc_token' KF_APD sh (sizeof t_run) pa2))
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
                kalloc_token' KF_APD sh (sizeof t_run) pa2 *
                KF_globals gv sh ls xx original_freelist_pointer
            in
            let freelist_only_pa2_null_case :=
                kalloc_token' KF_APD sh (sizeof t_run) pa1 * 
                KF_globals gv sh ls xx original_freelist_pointer
            in
            let freelist_both_null_case :=
                if eq_dec original_freelist_pointer nullval then
                    emp * KF_globals gv sh ls xx original_freelist_pointer
                else
                    (EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KF_globals gv sh ls' xx next *
                    kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer)
            in
            let both_pointers_case :=
                KF_globals gv sh (original_freelist_pointer::ls) xx pa1 *
                (*kalloc_token' KF_APD sh (sizeof t_run) pa1 *)
                kalloc_token' KF_APD sh (sizeof t_run) pa2
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

Definition KFGprog_clients: funspecs := KFGprog ++ [kalloc_write_pipe_spec; kfree_kalloc_spec; kalloc_write_42_spec; kalloc_write_42_kfree_spec].



Lemma body_kalloc_write_pipe: semax_body KFVprog KFGprog f_kalloc_write_pipe kalloc_write_pipe_spec.
Proof.
start_function.
forward.
forward_call (kalloc_spec_sub KF_APD t_struct_pipe) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold KF_globals. entailer!. 
- if_tac. (*destruct (eq_dec original_freelist_pointer nullval) eqn:e0.*)
    + forward_if.
        * rewrite H in H0; auto_contradict.
        * forward. entailer.
    + Intros ab. forward_if.
        rewrite mem_mgr_split. rewrite my_kalloc_token_split. Intros. rewrite kalloc_token_sz_split.
        Intros. 
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros. forward.
        forward. forward. forward. 
        entailer.
        Exists  (fst ab) (snd ab). entailer.
        unfold KF_globals. unfold pipe_rep.  Exists (fst (default_val t_struct_pipe)). entailer!.
        rewrite mem_mgr_split. entailer.
        * forward. entailer.
Qed.

Lemma body_kfree_kalloc: semax_body KFVprog KFGprog f_kfree_kalloc kfree_kalloc_spec.
Proof.
start_function.
forward_call (kfree_spec_sub KF_APD t_run) (new_head, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
    + destruct (eq_dec new_head nullval).
        *unfold KF_globals. entailer!.
        * unfold KF_globals. entailer!. 
            simplify_kalloc_token. 
    + destruct (eq_dec new_head nullval).
        *forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
        destruct (eq_dec original_freelist_pointer nullval).
            -- forward. Exists nullval. unfold KF_globals. entailer!.
            -- destruct ls.
                ++ forward. auto_contradict.
                ++ forward. Exists original_freelist_pointer. entailer. Exists v. entailer.
                    Exists ls. entailer. unfold KF_globals. entailer!. inversion H0; subst. entailer!.
                    simplify_kalloc_token. 
        *forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh, original_freelist_pointer::ls, xx, new_head ). (* kalloc *)
        destruct (eq_dec new_head nullval).
            -- forward.
            -- forward. Exists new_head. entailer. inversion H0; subst; entailer. unfold KF_globals. entailer!. simplify_kalloc_token.
Qed.


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
        * unfold my_kalloc_token. rewrite kalloc_token_sz_split. Intros.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. forward.
        forward. forward.
        Exists (Vint(Int.repr 42)) (fst ab) (snd ab). entailer.
        * forward.
Qed.

Lemma body_kalloc_write_42_kfree: semax_body KFVprog KFGprog f_kalloc_write_42_kfree kalloc_write_42_kfree_spec.
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
        * unfold my_kalloc_token. rewrite kalloc_token_sz_split. Intros.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros. forward.
        forward. 
        forward_call (kfree_spec_sub KF_APD tint) (original_freelist_pointer, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        -- if_tac_auto_contradict.
            unfold my_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
            sep_apply data_at_memory_block. entailer!.
        -- if_tac_auto_contradict.
            forward. Exists (Vint (Int.repr 42)).
            unfold KF_globals.
            inversion H0. rewrite H9; rewrite H10.
            entailer!.
        * forward.
Qed.

Lemma body_kfree_kalloc_twice: semax_body KFVprog KFGprog_clients f_kfree_kalloc_twice kfree_kalloc_twice_spec.
Proof.
start_function. destruct H.
forward_call (gv, sh, pa1, original_freelist_pointer, xx, ls).
- entailer!.
- Intros vret.
    if_tac.
    + if_tac.
        * if_tac.
            -- forward_call (gv, sh, pa2, original_freelist_pointer, xx, ls).
                ++ if_tac_auto_contradict.
                    entailer!.
                ++ if_tac_auto_contradict. Intros vret0.
                    if_tac_auto_contradict.
                    forward.
                    Exists vret0. entailer!.
                    destruct H6 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto.
            --forward_call (gv, sh, pa2, original_freelist_pointer, xx, ls).
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
        -- forward_call (gv, sh, pa2, original_freelist_pointer, xx, ls).
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
        -- Intros. forward_call (gv, sh, pa2, original_freelist_pointer, xx, ls).
            ++ if_tac_auto_contradict. entailer!.
            ++ if_tac_auto_contradict. 
                Intros vret0. forward.
                Exists vret0. entailer!.
                destruct H5 as [ [H11 [H12 H13]] | [[H21 H22] | [H31 [H32 H33]]] ]; auto_contradict.
                ** right. left; split; auto.
Qed.


Lemma body_kfree_kalloc_kfree_kalloc: semax_body KFVprog KFGprog f_kfree_kalloc_kfree_kalloc kfree_kalloc_kfree_kalloc_spec.
Proof.
start_function. Intros.
if_tac; if_tac; destruct H; 
forward_call (kfree_spec_sub KF_APD t_run) (pa1, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
- if_tac_auto_contradict. unfold KF_globals. entailer!.
- forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer). (* kalloc *)
    + if_tac_auto_contradict. entailer!.
    + if_tac_auto_contradict. 
        * forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
            -- if_tac_auto_contradict. entailer!.
            -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer). (* kalloc *)
                if_tac.
                    ++ forward. Exists nullval; unfold KF_globals. entailer!.
                    ++ Intros ab. destruct ls; auto_contradict.
        * Intros ab. destruct ls; auto_contradict. 
        forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
            -- entailer!.
            -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , snd ab, xx, fst ab). (* kalloc *)
                if_tac.
                    ++ forward. Exists (fst ab) (fst ab) (snd ab). if_tac.
                        ** unfold KF_globals. unfold my_kalloc_token. entailer!. repeat right. split; auto.
                        ** entailer.
                    ++ Intros ab0. forward. Exists (fst ab). unfold my_kalloc_token. rewrite mem_mgr_split. 
                        Exists (fst ab) (snd ab). if_tac_auto_contradict. Exists (fst ab0) (snd ab0). rewrite mem_mgr_split; entailer!.
                        repeat right; split; auto.
-if_tac_auto_contradict. unfold KF_globals. entailer!.
- forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer). (* kalloc *)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. 
    * forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
        -- if_tac_auto_contradict. unfold my_kalloc_token. entailer!.
        -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , (original_freelist_pointer :: ls), xx, pa2). (* kalloc *)
            if_tac.
                ++ forward.
                ++ Intros ab. destruct ls; auto_contradict;
                    forward; unfold my_kalloc_token, KF_globals; inversion H6; rewrite H3; rewrite H9; Exists pa2; entailer!;
                    do 4 right; left; split; auto.
    * Intros ab. destruct ls; auto_contradict.  
    forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
        -- if_tac_auto_contradict. unfold my_kalloc_token at 2. rewrite kalloc_token_sz_split. entailer!.
        -- if_tac_auto_contradict. rewrite mem_mgr_split. Intros. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
            ++ unfold my_kalloc_token. rewrite mem_mgr_split.  entailer!.
            ++ forward. if_tac_auto_contradict. Intros ab0. Exists pa2 (fst ab0) (snd ab0). rewrite mem_mgr_split. unfold KF_globals, my_kalloc_token. rewrite mem_mgr_split. entailer!.
               do 4 right. left; split; auto.
- if_tac_auto_contradict. unfold KF_globals. rewrite kalloc_token_sz_split. unfold my_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
- if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    ++ entailer!.
    ++ if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , snd ab, xx, fst ab). (* kalloc *)
        forward. if_tac_auto_contradict; inversion H5.
        ** Exists (fst ab). if_tac_auto_contradict.
        unfold my_kalloc_token, KF_globals. entailer!.
        do 2 right; left; split; auto.
        ** Intros ab0. Exists (fst ab). if_tac_auto_contradict.
            Exists (fst ab0) (snd ab0). unfold my_kalloc_token, KF_globals. entailer!.
            do 3 right; left; split; auto.
- if_tac_auto_contradict. unfold KF_globals. unfold my_kalloc_token. entailer!.
- if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    + if_tac_auto_contradict. unfold my_kalloc_token at 2; entailer!.
    + if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab0. forward. Exists pa2. unfold KF_globals. unfold my_kalloc_token; entailer!.
    inversion H8. rewrite H14, H15. inversion H5. rewrite H16, H17. entailer!.
Qed.

Lemma body_kfree_kfree_kalloc: semax_body KFVprog KFGprog f_kfree_kfree_kalloc kfree_kfree_kalloc_spec.
Proof.
start_function.
Intros.
if_tac; if_tac; destruct H; 
forward_call (kfree_spec_sub KF_APD t_run) (pa1, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
- if_tac_auto_contradict. unfold KF_globals. entailer!.
- if_tac_auto_contradict;
    forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , ls, xx, original_freelist_pointer). (* call kfree*)
    + if_tac_auto_contradict. entailer!.
    + if_tac_auto_contradict.
        forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer). (* kalloc *)
        if_tac_auto_contradict. 
        * forward. Exists nullval. unfold KF_globals. entailer!.
        * forward. Exists original_freelist_pointer. Exists (fst ab) (snd ab). entailer!. 
        unfold my_kalloc_token, KF_globals. entailer!.
-if_tac_auto_contradict. unfold KF_globals. entailer!.
-if_tac_auto_contradict;
forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , ls, xx,original_freelist_pointer). (* call kfree*)
+ if_tac_auto_contradict. entailer!. unfold my_kalloc_token; entailer!. 
+ if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. 
    forward. Exists pa2. unfold KF_globals. entailer!.
        * do 3 right. split; auto.
        * unfold my_kalloc_token. entailer!. inversion H0. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold KF_globals, my_kalloc_token. entailer!.
- if_tac_auto_contradict. 
forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , original_freelist_pointer::ls, xx,pa1). (* call kfree*)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab. forward. Exists pa1. unfold my_kalloc_token, KF_globals. entailer!.
    * do 2 right; left; split; auto.
    * inversion H6. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold my_kalloc_token, KF_globals. entailer!.
- if_tac_auto_contradict. forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , original_freelist_pointer::ls, xx,pa1). (* call kfree*)
    + if_tac_auto_contradict. unfold my_kalloc_token. entailer!.
    + if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , pa1::original_freelist_pointer::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. Intros ab.
    forward. Exists pa2. unfold KF_globals, my_kalloc_token. entailer!.
    inversion H6.
    entailer.
Qed.