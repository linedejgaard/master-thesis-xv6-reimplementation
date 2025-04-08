Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.client1.
Require Import VC.helper.
Require Import VC.VSU_kalloc_kfree_definitions.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
(*Definition Vprog : varspecs. mk_varspecs prog. Defined.*)

Definition MF_ASI: funspecs := Kalloc_ASI KF_APD _kalloc1 _kfree1.
Definition MF_imported_specs:funspecs := nil.
Definition MF_internal_specs: funspecs := MF_ASI.
Definition MF_globals gv : mpred:= ASI_kalloc.mem_mgr KF_APD gv.
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
 WITH (*sh : share, original_freelist_pointer:val, xx:Z, ls:list val,*) gv:globals
 PRE [ ] 
    PROP () PARAMS() GLOBALS(gv) SEP (MF_globals gv)
 POST [ tvoid ] 
    EX p: val, 
    PROP ( ) RETURN () SEP (
        (if eq_dec p nullval then
        emp
        else 
        kalloc_token' KF_APD Ews (sizeof t_struct_pipe) p *
        pipe_rep Ews p) 
        * MF_globals gv).
    
Definition client1_spec := 
    DECLARE _client1
    WITH new_head:val, gv:globals
    PRE [ tptr tvoid ]
        PROP(is_pointer_or_null new_head) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
            MF_globals gv *
            if eq_dec new_head nullval then emp
            else (kalloc_token' KF_APD Ews (sizeof t_run) new_head * data_at_ Ews t_run new_head)
        )
    POST [ tptr tvoid ]
        PROP( )
        RETURN (new_head) (* we return the head like in the pop function*)
        SEP (
            MF_globals gv *
            if eq_dec new_head nullval then emp
            else (kalloc_token' KF_APD Ews (sizeof t_run) new_head * data_at_ Ews t_run new_head) 
            ).

(* TODO should maybe add things to MFGprog... *)

Lemma body_client_11_pipealloc: semax_body MFVprog MFGprog f_client_11_pipealloc client_11_pipealloc_spec.
Proof.
start_function.
forward.
forward_call (t_struct_pipe, gv).  (* kalloc *)
- unfold MF_globals. entailer!.
- Intros vret. forward_if.
    + destruct (eq_dec vret nullval); entailer!. 
    + destruct (eq_dec vret nullval).
        * rewrite e in H. auto_contradict.
        * rewrite mem_mgr_split. Intros sh ls xx original_freelist_pointer.
        forward. forward. forward. forward. Exists vret.
        destruct (eq_dec vret nullval); auto_contradict.
        entailer.
        unfold pipe_rep. entailer!.
        unfold MF_globals. rewrite mem_mgr_split. Exists sh ls xx original_freelist_pointer. entailer!.
        apply derives_refl.
    + forward. Exists vret. destruct (eq_dec vret nullval); auto_contradict. entailer.
Qed.

Lemma body_client1: semax_body MFVprog MFGprog f_client1 client1_spec.
Proof.
start_function. 
forward_call (t_run, new_head , gv).  (* kfree *)
- unfold MF_globals. entailer!. 
destruct (eq_dec new_head nullval); entailer!. apply derives_refl.
- forward_call (t_run, gv).  (* kalloc *)
Intros vret. forward. (* same problem as before.. *)
Admitted.




