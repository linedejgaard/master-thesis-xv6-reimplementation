Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
Require Import VC.VSU_kalloc_kfree_definitions.
Require Import VC.Spec_kalloc.


#[export] Instance CompSpecs : compspecs. make_compspecs client1.prog. Defined.
(*Definition Vprog : varspecs. mk_varspecs prog. Defined.*)

Definition MF_ASI: funspecs := Kalloc_ASI KF_APD _kalloc1 _kfree1.
Definition MF_imported_specs:funspecs := nil.
Definition MF_internal_specs: funspecs := MF_ASI.
Definition MF_globals gv  sh ls xx original_freelist_pointer: mpred:= ASI_kalloc.mem_mgr KF_APD gv sh ls xx original_freelist_pointer.
Definition MFVprog : varspecs. mk_varspecs client1.prog. Defined.
Definition MFGprog: funspecs := MF_imported_specs ++ MF_internal_specs.

Local Open Scope logic.

(*Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.*)
(*Require Import VC.VSU_kalloc_kfree_definitions.*)

(*Definition Vprog : varspecs. mk_varspecs prog. Defined.*)


Definition client_11_pipealloc_spec : ident * funspec :=
 DECLARE _client_11_pipealloc
 WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
 PRE [ ] 
    PROP () PARAMS() GLOBALS(gv) SEP (MF_globals gv sh ls xx original_freelist_pointer)
 POST [ tvoid ] 
    PROP ( ) RETURN () SEP (
        (if eq_dec original_freelist_pointer nullval then
            MF_globals gv  sh ls xx original_freelist_pointer *emp
        else
        EX next ls',
          (!! (next :: ls' = ls) &&
                pipe_rep sh original_freelist_pointer *
                MF_globals gv  sh ls' xx next
        )
        )
    ).
    
Definition client1_spec := 
    DECLARE _client1
    WITH new_head:val, sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ tptr tvoid ]
        PROP(is_pointer_or_null new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            MF_globals gv  sh ls xx original_freelist_pointer *
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
            
            (if eq_dec new_head nullval then 
                (if (eq_dec original_freelist_pointer nullval) then 
                    (emp *  MF_globals gv  sh ls xx original_freelist_pointer)
                else (
                    (EX next ls',
                    (!! (next :: ls' = ls) &&
                        MF_globals gv  sh ls' xx next
                    ) *  
                    kalloc_token' KF_APD sh (sizeof t_run) original_freelist_pointer)))
            else (
                MF_globals gv  sh ls xx original_freelist_pointer* (* is this still wrong?? *)
                kalloc_token' KF_APD sh (sizeof t_run) new_head) )
            ).

Definition client12_42_spec : ident * funspec :=
    DECLARE _client12_42
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (MF_globals gv sh ls xx original_freelist_pointer)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec original_freelist_pointer nullval then
                (!! (r = Vint (Int.repr 0)) &&
                MF_globals gv  sh ls xx original_freelist_pointer * emp)
            else
            EX next ls',
                (!! (next :: ls' = ls /\
                    r = Vint (Int.repr 42)
                 ) &&
                    data_at sh tint (Vint (Int.repr 42)) original_freelist_pointer *
                    MF_globals gv  sh ls' xx next
            )
            )
        ).

Definition client12_42_include_free_spec : ident * funspec :=
    DECLARE _client12_42_include_free
    WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
    PRE [ ] 
        PROP () PARAMS() GLOBALS(gv) SEP (MF_globals gv sh ls xx original_freelist_pointer)
    POST [ tint ] 
        EX r,
        PROP ( ) RETURN (r) SEP (
            (if eq_dec original_freelist_pointer nullval then
                (!! (r = Vint (Int.repr 0)) &&
                MF_globals gv  sh ls xx original_freelist_pointer)
            else
                (!! ( r = Vint (Int.repr 42) ) &&
                MF_globals gv  sh ls xx original_freelist_pointer)
            )
        ).
        

                            
(* TODO should maybe add things to MFGprog... *)

Lemma body_client_11_pipealloc: semax_body MFVprog MFGprog f_client_11_pipealloc client_11_pipealloc_spec.
Proof.
start_function.
forward.
forward_call (kalloc1_spec_sub KF_APD t_struct_pipe) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
(*forward_call ((sizeof t_struct_pipe), gv,  sh,  ls , xx,  original_freelist_pointer).*)
- unfold MF_globals. entailer!. 
- if_tac. (*destruct (eq_dec original_freelist_pointer nullval) eqn:e0.*)
    + forward_if.
        * rewrite H in H0; auto_contradict.
        * forward. entailer.
    + Intros ab. forward_if.
       (* *
        rewrite mem_mgr_split. rewrite my_kalloc_token_split. Intros. rewrite kalloc_token_sz_split.
        Intros. entailer!.*)
        *
        rewrite mem_mgr_split. rewrite my_kalloc_token_split. Intros. rewrite kalloc_token_sz_split.
        Intros. 
        rewrite memory_block_data_at_; auto. rewrite data_at__eq. Intros. forward.
        forward. forward. forward. 
        entailer.
        Exists  (fst ab) (snd ab). entailer.
        unfold MF_globals. unfold pipe_rep.  Exists (fst (default_val t_struct_pipe)). entailer!.
        rewrite mem_mgr_split. entailer.
        * forward. entailer.
Qed.

Lemma body_client1: semax_body MFVprog MFGprog f_client1 client1_spec.
Proof.
start_function.
forward_call (kfree1_spec_sub KF_APD t_run) (new_head, gv, sh , ls, xx, original_freelist_pointer). (* call kfree *)
    + destruct (eq_dec new_head nullval).
        *unfold MF_globals. entailer!.
        * unfold MF_globals. entailer!. 
            simplify_kalloc_token. 
    + destruct (eq_dec new_head nullval).
        *forward_call (kalloc1_spec_sub KF_APD t_run) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
        destruct (eq_dec original_freelist_pointer nullval).
            -- forward. Exists nullval. unfold MF_globals. entailer!.
            -- destruct ls.
                ++ forward. auto_contradict.
                ++ forward. Exists original_freelist_pointer. entailer. Exists v. entailer.
                    Exists ls. entailer. unfold MF_globals. entailer!. inversion H0; subst. entailer!.
                    simplify_kalloc_token. 
        *forward_call (kalloc1_spec_sub KF_APD t_run) (gv, sh, original_freelist_pointer::ls, xx, new_head ). (* kalloc *)
        destruct (eq_dec new_head nullval).
            -- forward.
            -- forward. Exists new_head. entailer. inversion H0; subst; entailer. unfold MF_globals. entailer!. simplify_kalloc_token.
Qed.


Lemma body_client12_42: semax_body MFVprog MFGprog f_client12_42 client12_42_spec.
Proof.
start_function.
forward. 
forward_call (kalloc1_spec_sub KF_APD tint) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold MF_globals. entailer!.
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

Lemma body_client12_42_include_free: semax_body MFVprog MFGprog f_client12_42_include_free client12_42_include_free_spec.
Proof.
    start_function.
    forward. 
    forward_call (kalloc1_spec_sub KF_APD tint) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
    - unfold MF_globals. entailer!.
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
        forward_call (kfree1_spec_sub KF_APD tint) (original_freelist_pointer, gv, sh , snd ab, xx, (fst ab)). (* call kfree *)
        -- if_tac; auto_contradict.
            unfold my_kalloc_token. rewrite kalloc_token_sz_split. entailer!.
            sep_apply data_at_memory_block. entailer!.
        -- if_tac; auto_contradict.
            forward. Exists (Vint (Int.repr 42)).
            unfold MF_globals.
            inversion H0. rewrite H9; rewrite H10.
            entailer!.
        * forward.
Qed.