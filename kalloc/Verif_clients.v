Require Import VST.floyd.proofauto.

Require Import VC.ASI_kalloc.
Require Import VC.kalloc_kfree_definitions.
Require Import VC.Spec_kalloc.
Require Import VC.clientsfun.
Require Import VC.tactics.

Require Import VC.kalloc.



Local Open Scope logic.


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
            let both_is_pointers_case :=
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
                else both_is_pointers_case
        ).



Definition kalloc_write_42_kfree_kfree_spec : ident * funspec :=
    DECLARE _kalloc_write_42_kfree_kfree
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
Definition kfree_kfree_kalloc_loop_spec := 
    DECLARE _kfree_kfree_kalloc_loop
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, next:val
    PRE [ tptr tvoid ]
        PROP(
            isptr pa1 /\ (* just assume it is pointers for simplicity *)
            Int.min_signed <= Int.signed (Int.repr 2) + Int.signed (Int.repr 1) <= Int.max_signed
        ) 
        PARAMS (pa1) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (2)%nat pa1 PGSIZE t_run *
            KF_globals gv sh ls xx original_freelist_pointer
        )
    POST [ tptr tvoid ]
        PROP( )
            RETURN (offset_val PGSIZE pa1) (* we return the head like in the pop function*)
            SEP 
            (
                (*data_at sh t_run pa1 (offset_val PGSIZE pa1) **)
                kalloc_token' KF_APD sh (sizeof t_run) (offset_val PGSIZE pa1) *
                KF_globals gv sh (original_freelist_pointer::ls) xx pa1
                ).

Definition kfree_loop_spec := 
    DECLARE _kfree_loop
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KF_globals gv sh ls xx original_freelist_pointer
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
                KF_globals gv sh (added_elem++ls) xx head
            ).

Definition kfree_loop_kalloc_spec := 
    DECLARE _kfree_loop_kalloc
    WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z
    PRE [ tptr tvoid, tint ]
        PROP(
            isptr pa1 /\
            Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
            0 <= n <= Int.max_signed
        ) 
        PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
        SEP (
            kalloc_tokens Tok_APD sh (Z.to_nat n)%nat pa1 PGSIZE t_run *
            KF_globals gv sh ls xx original_freelist_pointer
        )
    POST [ tptr tvoid ]
        EX head, EX added_elem, (* TODO: fix top and next is the same?? *)
        PROP( 
            (* before alloc *)
            added_elem = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE original_freelist_pointer) /\
            head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE original_freelist_pointer)++ls))
            )
            RETURN (head) (* we return the head like in the pop function*)
            SEP 
            (
            let n_eq_0_case :=
                if eq_dec original_freelist_pointer nullval then
                emp * KF_globals gv sh ls xx original_freelist_pointer
            else
                EX next, EX ls',
                    !! (next :: ls' = ls) &&
                    KF_globals gv sh ls' xx next *
                    kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer
            in
            let n_gt_0_case :=
                KF_globals gv sh ((tl added_elem)++ls) xx (hd nullval added_elem) *
                kalloc_token' KF_APD sh (sizeof t_run) head
            in
            if (Z.ltb 0 n) then
                n_gt_0_case
            else 
                n_eq_0_case
                ).

Definition kalloc_int_array_spec : ident * funspec :=
    DECLARE _kalloc_int_array
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
Compute (sizeof t_struct_pipe).

Definition KFGprog_clients: funspecs := KFGprog ++ [kalloc_write_pipe_spec; kfree_kalloc_spec; kalloc_write_42_spec; kalloc_write_42_kfree_spec; kfree_loop_spec].

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
        rewrite mem_mgr_split. rewrite type_kalloc_token_split. Intros. rewrite kalloc_token_sz_split.
        Intros. 
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros. forward.
        forward. forward. forward. 
        entailer.
        Exists  (fst ab) (snd ab). entailer.
        unfold KF_globals. unfold pipe_rep.  Exists (fst (default_val t_struct_pipe)). entailer!.
        rewrite mem_mgr_split. entailer.
        * forward. entailer.
Qed.

Ltac simplify_kalloc_token :=
  repeat (
    rewrite kalloc_token_sz_split;
    unfold type_kalloc_token
  );
  entailer!.


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
        * unfold type_kalloc_token. rewrite kalloc_token_sz_split. Intros.
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
        * unfold type_kalloc_token. rewrite kalloc_token_sz_split. Intros.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros. forward.
        forward. 
        forward_call (kfree_spec_sub KF_APD tint) (original_freelist_pointer, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        -- if_tac_auto_contradict.
            unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
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
                        ** unfold KF_globals. unfold type_kalloc_token. entailer!. repeat right. split; auto.
                        ** entailer.
                    ++ Intros ab0. forward. Exists (fst ab). unfold type_kalloc_token. rewrite mem_mgr_split. 
                        Exists (fst ab) (snd ab). if_tac_auto_contradict. Exists (fst ab0) (snd ab0). rewrite mem_mgr_split; entailer!.
                        repeat right; split; auto.
-if_tac_auto_contradict. unfold KF_globals. entailer!.
- forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer). (* kalloc *)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. 
    * forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
        -- if_tac_auto_contradict. unfold type_kalloc_token. entailer!.
        -- if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , (original_freelist_pointer :: ls), xx, pa2). (* kalloc *)
            if_tac.
                ++ forward.
                ++ Intros ab. destruct ls; auto_contradict;
                    forward; unfold type_kalloc_token, KF_globals; inversion H6; rewrite H3; rewrite H9; Exists pa2; entailer!;
                    do 4 right; left; split; auto.
    * Intros ab. destruct ls; auto_contradict.  
    forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
        -- if_tac_auto_contradict. unfold type_kalloc_token at 2. rewrite kalloc_token_sz_split. entailer!.
        -- if_tac_auto_contradict. rewrite mem_mgr_split. Intros. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
            ++ unfold type_kalloc_token. rewrite mem_mgr_split.  entailer!.
            ++ forward. if_tac_auto_contradict. Intros ab0. Exists pa2 (fst ab0) (snd ab0). rewrite mem_mgr_split. unfold KF_globals, type_kalloc_token. rewrite mem_mgr_split. entailer!.
               do 4 right. left; split; auto.
- if_tac_auto_contradict. unfold KF_globals. rewrite kalloc_token_sz_split. unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
- if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    ++ entailer!.
    ++ if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , snd ab, xx, fst ab). (* kalloc *)
        forward. if_tac_auto_contradict; inversion H5.
        ** Exists (fst ab). if_tac_auto_contradict.
        unfold type_kalloc_token, KF_globals. entailer!.
        do 2 right; left; split; auto.
        ** Intros ab0. Exists (fst ab). if_tac_auto_contradict.
            Exists (fst ab0) (snd ab0). unfold type_kalloc_token, KF_globals. entailer!.
            do 3 right; left; split; auto.
- if_tac_auto_contradict. unfold KF_globals. unfold type_kalloc_token. entailer!.
- if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab.
    forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , snd ab, xx, fst ab). (* call kfree *)
    + if_tac_auto_contradict. unfold type_kalloc_token at 2; entailer!.
    + if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , fst ab::snd ab, xx, pa2). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab0. forward. Exists pa2. unfold KF_globals. unfold type_kalloc_token; entailer!.
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
        unfold type_kalloc_token, KF_globals. entailer!.
-if_tac_auto_contradict. unfold KF_globals. entailer!.
-if_tac_auto_contradict;
forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , ls, xx,original_freelist_pointer). (* call kfree*)
+ if_tac_auto_contradict. entailer!. unfold type_kalloc_token; entailer!. 
+ if_tac_auto_contradict.
    forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. 
    forward. Exists pa2. unfold KF_globals. entailer!.
        * do 3 right. split; auto.
        * unfold type_kalloc_token. entailer!. inversion H0. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold KF_globals, type_kalloc_token. entailer!.
- if_tac_auto_contradict. 
forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , original_freelist_pointer::ls, xx,pa1). (* call kfree*)
+ if_tac_auto_contradict. entailer!.
+ if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , original_freelist_pointer::ls, xx, pa1). (* kalloc *)
    if_tac_auto_contradict.
    Intros ab. forward. Exists pa1. unfold type_kalloc_token, KF_globals. entailer!.
    * do 2 right; left; split; auto.
    * inversion H6. rewrite H9, H10. entailer.
- if_tac_auto_contradict. unfold type_kalloc_token, KF_globals. entailer!.
- if_tac_auto_contradict. forward_call (kfree_spec_sub KF_APD t_run) (pa2, gv, sh , original_freelist_pointer::ls, xx,pa1). (* call kfree*)
    + if_tac_auto_contradict. unfold type_kalloc_token. entailer!.
    + if_tac_auto_contradict. forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , pa1::original_freelist_pointer::ls, xx, pa2). (* kalloc *)
    if_tac_auto_contradict. Intros ab.
    forward. Exists pa2. unfold KF_globals, type_kalloc_token. entailer!.
    inversion H6.
    entailer.
Qed.


Lemma body_kalloc_write_42_kfree_kfree: semax_body KFVprog KFGprog f_kalloc_write_42_kfree_kfree kalloc_write_42_kfree_kfree_spec.
Proof.
    start_function.
    forward. 
    forward_call (kalloc_spec_sub KF_APD tint) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
    - unfold KF_globals. entailer!.
    - if_tac.
    + forward_if.
        * rewrite H in H0; auto_contradict.
        * forward_call (kfree_spec_sub KF_APD t_run) (original_freelist_pointer, gv, sh , ls, xx,original_freelist_pointer). (* call kfree*)
            -- if_tac_auto_contradict. entailer!.
            -- rewrite H. simpl. auto.
            -- if_tac_auto_contradict. 
            forward. Exists (Vint(Int.repr 0)). entailer.
    + Intros ab.
      destruct ls; auto_contradict.
      forward_if.
        * unfold type_kalloc_token. rewrite kalloc_token_sz_split. Intros.
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros. forward.
        forward. 
        forward_call (kfree_spec_sub KF_APD tint) (original_freelist_pointer, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        -- if_tac_auto_contradict.
            unfold type_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
            sep_apply data_at_memory_block. entailer!.
        -- if_tac_auto_contradict.
            forward. Exists (Vint (Int.repr 42)).
            unfold KF_globals.
            inversion H0. rewrite H9; rewrite H10.
            entailer!.
        * rewrite H1 in H. auto_contradict.
Qed.


Lemma body_kfree_kfree_kalloc_loop: semax_body  KFVprog KFGprog f_kfree_kfree_kalloc_loop kfree_kfree_kalloc_loop_spec.
Proof.
    start_function.
    Intros. forward. (*forward. unfold abb iate in POSTCONDITION.*)
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= 2 /\
        ((curr_head = original_freelist_pointer /\ i = 0) \/ (curr_head = (offset_val (-PGSIZE) (p_tmp))  /\ i <> 0)) /\
        tmp_added_elem = (pointers_with_original_head (Z.to_nat i) (pa1) PGSIZE original_freelist_pointer) /\
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
        KF_globals gv sh (tmp_added_elem ++ ls) xx curr_head *
        kalloc_tokens Tok_APD sh (Z.to_nat(2-i)) p_tmp (PGSIZE) t_run
        )
        )
    )%assert; destruct H as [H H3].
    - entailer. Exists 0 pa1 original_freelist_pointer (pointers_with_original_head (Z.to_nat 0) pa1 PGSIZE original_freelist_pointer). (*entailer. *)
        rewrite <- pointers_with_head_empty. simpl; entailer!; unfold offset_val in H2; destruct pa1; auto_contradict.
    - entailer.
    - Intros. destruct (Z.to_nat (2 - i)) eqn:e.
        +assert (i = 2); try rep_lia.
        + forward_call (kfree_spec_sub KF_APD t_run) (p_tmp, gv, sh , (tmp_added_elem ++ ls), xx,curr_head). (* call kfree*)
            * if_tac; destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
                -- unfold offset_val in H1. destruct pa1; auto_contradict.
                --unfold KF_globals. unfold type_kalloc_token. rewrite kalloc_token_sz_split. simpl. rewrite kalloc_token_sz_split. Intros.
                entailer!.
            * destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04. unfold is_pointer_or_null.
              unfold offset_val. destruct pa1; auto_contradict; auto.
            * forward. entailer!. destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04. unfold is_pointer_or_null.
            unfold offset_val. destruct pa1; auto_contradict; auto.
            forward. if_tac; auto_contradict; destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
                -- unfold offset_val in H1. destruct pa1; auto_contradict.
                -- Exists ((((i+1)%Z, (offset_val PGSIZE p_tmp):val), p_tmp:val), (curr_head::(pointers_with_original_head(Z.to_nat (i)) pa1 PGSIZE)original_freelist_pointer):list val).
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
                ++ unfold KF_globals. 
                assert (Z.to_nat (2 - (i + 1)) = n); try rep_lia.
                rewrite H6. rewrite app_comm_cons. entailer!.
    - forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , pa1::original_freelist_pointer::ls, xx, offset_val PGSIZE pa1). (* kalloc *)
        +
        (*- forward_call (sh, add_offset pa1 PGSIZE, xx, (pa1::original_freelist_pointer::ls), gv). (* call kalloc *)*)
        entailer. destruct H0 as [H01 [H02 [H03 [H04 H05]]]]; rewrite H04 in H1.
        unfold KF_globals. rewrite H03.
        rewrite mem_mgr_split.
         
        assert (i = 2); try rep_lia. rewrite H0. destruct (0 <? Z.to_nat 2)%nat eqn:ei; try rep_lia.
        * destruct H02 as [[H021 H022] | [H031 H032]]; try rep_lia.
          rewrite H04 in H031. rewrite sub_add_offset_n in H031; auto; try rep_lia.
          Intros.
          destruct (Z.to_nat 2) eqn:e2; auto_contradict.
          unfold pointers_with_original_head.
          destruct n eqn:en; try rep_lia.
          destruct n0 eqn:en0; try rep_lia.
          simpl. rewrite mem_mgr_split. refold_freelistrep. entailer!.
          unfold PGSIZE; rep_lia.
        * rewrite Nat.ltb_ge in ei. try rep_lia.
        + destruct H0 as [H01 [H02 [H03 [H04 H05]]]].
        forward. if_tac.
        assert (isptr (offset_val PGSIZE pa1)). {
            apply isptr_offset_val'; auto.
        }
        rewrite H1 in H2; auto_contradict.
        Intros ab. unfold type_kalloc_token, KF_globals. 
        inversion H2. entailer!.
Qed.


Lemma body_kfree_loop: semax_body KFVprog KFGprog f_kfree_loop kfree_loop_spec.
Proof.
start_function.
Intros. forward. (*forward. unfold abb iate in POSTCONDITION.*)
    forward_while 
    (EX i:Z, EX p_tmp:val, EX curr_head:val, EX tmp_added_elem : list val,
    PROP  (
        0 <= i <= n /\
        ((curr_head = original_freelist_pointer /\ i = 0) \/ (curr_head = (offset_val (-PGSIZE) (p_tmp))  /\ i <> 0)) /\
        tmp_added_elem = (pointers_with_original_head (Z.to_nat i) (pa1) PGSIZE original_freelist_pointer) /\
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
            KF_globals gv sh (tmp_added_elem ++ ls) xx curr_head *
            kalloc_tokens Tok_APD sh (Z.to_nat(n-i)) p_tmp (PGSIZE) t_run
        )
    ))%assert; destruct H as [H01 [H02 H03]].
    - entailer. Exists 0 pa1 original_freelist_pointer (pointers_with_original_head (Z.to_nat 0) pa1 PGSIZE original_freelist_pointer). (*entailer. *)
        rewrite <- pointers_with_head_empty. entailer. destruct (Z.to_nat n).
            + rewrite <- H0 in H01. try rep_lia.
            + rewrite app_nil_l. entailer!.
    - entailer.
    - Intros. destruct (Z.to_nat (n - i)) eqn:e1.
        + try rep_lia.
        + forward_call (kfree_spec_sub KF_APD t_run) (p_tmp, gv, sh , (tmp_added_elem ++ ls), xx,curr_head). (* call kfree*)
        (*forward_call (sh, p_tmp, curr_head, xx, gv, (tmp_added_elem ++ ls), PGSIZE). (* call kfree1 *)*)
            *if_tac; destruct H0 as [H001 [H002 [H003 [H04 H05]]]]. rewrite H04 in H.
            -- unfold offset_val in H. destruct pa1; auto_contradict.
            --unfold KF_globals. unfold type_kalloc_token. rewrite kalloc_token_sz_split. simpl. rewrite kalloc_token_sz_split. Intros.
            entailer!.
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
                ++ Exists ((((i+1)%Z, (offset_val PGSIZE p_tmp):val), p_tmp:val), ((pointers_with_original_head(Z.to_nat (i+1)) pa1 PGSIZE)original_freelist_pointer):list val).
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
                    ** unfold KF_globals.
                    

                    assert (Z.to_nat (n - (i + 1)) = n0); try rep_lia.
                    rewrite H0.
                    assert (curr_head :: tmp_added_elem = pointers_with_original_head (Z.to_nat (i + 1)) pa1 PGSIZE original_freelist_pointer). {
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


Lemma body_kfree_loop_kalloc: semax_body KFVprog KFGprog_clients f_kfree_loop_kalloc kfree_loop_kalloc_spec.
Proof.
start_function.
forward_call (sh, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z).
- destruct H as [H1 [H2 H3]]; auto.
- Intros vret. 
forward_call (kalloc_spec_sub KF_APD t_run) (gv, sh , snd vret ++ ls, xx,  fst vret ); (* kalloc *)
destruct H as [H11 [H12 H13]]; auto.
    + unfold KF_globals. entailer!.
    + if_tac; auto_contradict.
        * forward. destruct (Z.to_nat n) eqn:en.
            -- assert (n = 0); try rep_lia. rewrite H3. Exists (fst vret) (snd vret).
                    entailer.
                    if_tac_auto_contradict;
                    destruct (0 <? 0) eqn:efalse; try rep_lia.
                ++simpl in H0. rewrite H0. simpl in H1. rewrite H1. unfold KF_globals. rewrite app_nil_l. entailer!.
                ++simpl in H1. rewrite <- H1 in H3. rewrite H in H3; auto_contradict.
            -- rewrite <- add_to_pointers_with_head in H1; auto; try rep_lia. simpl in H1.
            assert (isptr (offset_val (Z.of_nat (n0 - 0) * PGSIZE) pa1)). { apply isptr_offset_val'. auto. }
            rewrite <- H1 in H3. rewrite H in H3; auto_contradict.
        * forward. destruct (Z.to_nat n) eqn:en.
            -- Exists (fst vret) (snd vret).
                assert (n = 0); try rep_lia. rewrite H4.
                if_tac_auto_contradict;
                destruct (0 <? 0) eqn:efalse; try rep_lia.
                ++ unfold KF_globals. entailer!.
                ++ destruct ls eqn:els.
                    **  simpl in H0. rewrite H0 in H3. inversion H3.
                    ** simpl in H1. simpl in H0. Exists (fst ab) (snd ab). unfold KF_globals. rewrite H1.
                    entailer!. rewrite H0 in H3. rewrite app_nil_l in H3. auto.
                    unfold type_kalloc_token. entailer!.
            -- Exists (fst vret) (snd vret).
                entailer.
                destruct (0 <? n) eqn:etrue; try rep_lia.
                unfold KF_globals. unfold type_kalloc_token. entailer!.
                destruct (snd vret).
                ++ replace (S n0) with (n0 + 1)%nat in H0; try rep_lia. 
                destruct n0 eqn:en0.
                ** simpl in H0. inversion H0.
                ** rewrite  <- add_to_pointers_with_head in H0; auto; try rep_lia. inversion H0.
                ++ simpl. rewrite <- app_comm_cons in H3. inversion H3. entailer.
Qed.