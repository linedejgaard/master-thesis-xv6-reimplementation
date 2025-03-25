Require Import VST.floyd.proofauto.
Require Import VC.simple_kfree_file.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_run := Tstruct _run noattr.

Definition t_struct_kmem := Tstruct _struct_kmem noattr.


Definition kfree1_spec := 
 DECLARE _kfree1
   WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals
   PRE [ tptr tvoid]
      PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) 
      PARAMS (new_head) GLOBALS(gv)
      SEP (data_at sh (t_run) nullval new_head; 
      data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
      )
   POST [ tvoid ]
      PROP()
      RETURN () 
      SEP (
         data_at sh (t_run) (original_freelist_pointer) new_head; 
         data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
         ).

(* I THINK THIS IS WRONG, BECAUSE I DON'T THEY THEY ARE DISJOINT: *)
Definition kfree1_1_spec := 
 DECLARE _kfree1
   WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals
   PRE [ tptr tvoid]
      PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) 
      PARAMS (new_head) GLOBALS(gv)
      SEP (data_at sh (t_run) nullval new_head * 
      data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
      )
   POST [ tvoid ]
      PROP()
      RETURN ()
      SEP (
         data_at sh (t_run) (original_freelist_pointer) new_head * (* the new head should point to the original freelist pointer *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem) (** the top of the freelist should point to the new head *)
         ).


Definition call_kfree1_spec := 
   DECLARE _call_kfree1
      WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals
      PRE [ tptr tvoid]
         PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) (* writable_share is necessary *)
         PARAMS (new_head) GLOBALS(gv)
         SEP (data_at sh (t_run) nullval new_head; (* the input run struct should exists *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* the kmem freelist should exists, xx is a placeholder for the spinlock *)
         )
      POST [ tvoid ]
         PROP()
         RETURN () (* no return value *)
         SEP (
            data_at sh (t_run) (original_freelist_pointer) new_head; (* the new head should point to the original freelist pointer *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem) (** the top of the freelist should point to the new head *)
            ).
   
   Definition call_kfree1_if_1_spec := 
      DECLARE _call_kfree1_if_1
         WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals
         PRE [ tptr tvoid]
            PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) 
            PARAMS (new_head) GLOBALS(gv)
            SEP (data_at sh (t_run) nullval new_head;
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
            )
         POST [ tvoid ]
            PROP()
            RETURN () 
            SEP (
               if (eq_dec new_head nullval) then
               data_at sh (t_run) nullval new_head * 
               data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
               else 
               data_at sh (t_run) (original_freelist_pointer) new_head *
               data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem) 
               ).

(************** pointer comparison **************'*)


Definition pointer_comparison (p q : val) (cmp : comparison) : val :=
   force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp cmp p q))).
Definition pointer_cmp_bool (p q : val) (cmp : comparison) : bool :=
   eq_dec (pointer_comparison p q cmp) (Vint (Int.repr 1)).
Definition pointer_le_bool (p q : val) : bool :=
   pointer_cmp_bool p q Cle.
              

Definition freerange_no_loop_no_add_spec :=
   DECLARE _freerange_no_loop_no_add
      WITH sh : share, new_head : val, pa_end : val, 
            original_freelist_pointer : val, xx : Z, gv : globals
      PRE [ tptr tvoid, tptr tvoid ]
         PROP (
            writable_share sh;
            is_pointer_or_null original_freelist_pointer
         ) 
         PARAMS (new_head; pa_end) GLOBALS (gv)
         SEP (
            denote_tc_test_order new_head pa_end &&
            (data_at sh (t_run) nullval new_head *
            data_at sh t_struct_kmem 
               (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
         )
      POST [ tvoid ]
         PROP ()
         RETURN ()
         SEP (
            (*denote_tc_test_order new_head pa_end **)
            if pointer_le_bool new_head pa_end then
               data_at sh (t_run) original_freelist_pointer new_head *
               data_at sh t_struct_kmem 
                  (Vint (Int.repr xx), new_head) (gv _kmem) 
            else
               data_at sh (t_run) nullval new_head * 
                  data_at sh t_struct_kmem 
                     (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
         ).

Definition Gprog : funspecs := [
kfree1_spec; kfree1_1_spec ; 
call_kfree1_spec; 
call_kfree1_if_1_spec; freerange_no_loop_no_add_spec].

Lemma body_kfree1: semax_body Vprog Gprog f_kfree1 kfree1_spec.
Proof. start_function. repeat forward. entailer!. Qed.

Lemma body_kfree1_1: semax_body Vprog Gprog f_kfree1 kfree1_1_spec.
Proof. start_function. Intros. repeat forward. entailer!. Qed.

Lemma body_call_kfree1: semax_body Vprog Gprog f_call_kfree1 call_kfree1_spec.
Proof. start_function. forward_call. entailer!. Qed.

Lemma body_call_kfree1_if_1_spec: semax_body Vprog Gprog f_call_kfree1_if_1 call_kfree1_if_1_spec.
Proof.
start_function.
forward_if.
- forward_call.
  entailer!.
  destruct (eq_dec new_head nullval); entailer!.
- forward. entailer!. destruct (eq_dec nullval nullval); entailer!.
Qed.


Lemma cmp_le_is_either_0_or_1 : forall p q i,
   sem_cmp_pp Cle p q = Some (Vint i) ->
   (i = Int.zero) \/ (i = Int.one).
Proof.
intros.
destruct (eq_dec i Int.zero). left; auto.
destruct (eq_dec i Int.one). right; auto.
unfold sem_cmp_pp in H. inversion H.
unfold bool2val in H1. unfold Z.b2z in H1. unfold option_map in H1.
destruct (Val.cmplu_bool true2 Cle p q).
- destruct b; inversion H1; exfalso.
   + apply n0; auto.
   + apply n; auto.
- inversion H1.
Qed.

Lemma body_freerange_no_loop_no_add: semax_body Vprog Gprog f_freerange_no_loop_no_add freerange_no_loop_no_add_spec.
Proof. start_function.
forward_if. 
   -apply andp_left1. entailer!.
   -forward_call (sh, new_head, original_freelist_pointer, xx, gv).
      +apply andp_left2. entailer!.
      +entailer. destruct (pointer_le_bool new_head pa_end) eqn:e; try discriminate; try contradiction. 
         * entailer!. 
         * unfold pointer_le_bool in e.
           unfold pointer_cmp_bool in e. 
           unfold pointer_comparison in e.
           destruct (sem_cmp_pp Cle new_head pa_end) eqn:e1. 
           --destruct v; try discriminate; try contradiction.
             apply typed_true_tint_Vint in H0.
             exfalso; apply H0.
             apply cmp_le_is_either_0_or_1 in e1. destruct e1; auto.
             rewrite H5 in e.
             simpl in e. inversion e.
           --entailer!.
   - forward. entailer. destruct (pointer_le_bool new_head pa_end) eqn:e1.
      + destruct (sem_cmp_pp Cle new_head pa_end ) eqn:e2; try contradiction; try discriminate.
        destruct v; try discriminate; try contradiction.
        apply typed_false_tint_Vint in H0.
        rewrite H0 in e2. unfold pointer_le_bool in e1. unfold pointer_cmp_bool in e1.
        unfold pointer_comparison in e1.
        rewrite e2 in e1. inversion e1.
      + apply andp_left2. entailer!.
Qed.      