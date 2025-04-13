Require Import VST.floyd.proofauto.

Require Import VC.ASI_kalloc.
Require Import VC.kallocfun.
Require Import VC.Spec_kalloc.
Require Import VC.clientsfun.
Require Import VC.tactics.

Require Import VC.kalloc.

Local Open Scope logic.


Definition kalloc_write_pipe_spec : ident * funspec :=
 DECLARE _kalloc_write_pipe
 WITH sh : share, original_freelist_pointer:val, xx:Z, ls:list val, gv:globals
 PRE [ ] 
    PROP () PARAMS() GLOBALS(gv) SEP (KAF_globals gv sh ls xx original_freelist_pointer)
 POST [ tvoid ]
    PROP ( ) RETURN () SEP (
        (if eq_dec original_freelist_pointer nullval then
            KAF_globals gv  sh ls xx original_freelist_pointer *emp
        else
        EX next ls',
          (!! (next :: ls' = ls) &&
                pipe_rep sh original_freelist_pointer *
                KAF_globals gv  sh ls' xx next
        )
        )
    ).


Lemma body_kalloc_write_pipe: semax_body KAFVprog KAFGprog f_kalloc_write_pipe kalloc_write_pipe_spec.
Proof.
start_function.
forward.
forward_call (kalloc_spec_sub KAF_APD t_struct_pipe) (gv, sh , ls, xx, original_freelist_pointer ). (* kalloc *)
- unfold KAF_globals. entailer!. 
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
        unfold KAF_globals. unfold pipe_rep.  Exists (fst (default_val t_struct_pipe)). entailer!.
        rewrite mem_mgr_split. entailer.
        * forward. entailer.
Qed.