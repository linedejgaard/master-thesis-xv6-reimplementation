Require Import VST.floyd.proofauto.
Require Import VC.client1.
Require Import VC.helper.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(************************ specs *********************************)
Definition kfree1_spec := 
    DECLARE _kfree1
       WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, size:Z, number_structs_available:nat
       PRE [ tptr tvoid]
          PROP(
               writable_share sh /\
               is_pointer_or_null original_freelist_pointer /\
               (Nat.le (S O) (number_structs_available)) (* there is at least one available *)
               ) 
          PARAMS (new_head) GLOBALS(gv)
          SEP (
             freelistrep sh n original_freelist_pointer *
             available sh number_structs_available new_head PGSIZE *
             (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) )
          )
       POST [ tvoid ]
          PROP()
          RETURN () 
          SEP (
             freelistrep sh (S n) new_head *
             available sh (Nat.sub number_structs_available (S O)) (add_offset new_head PGSIZE) PGSIZE *
             data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem)
             ).

Definition kalloc1_spec := (* kind of pop *)
DECLARE _kalloc1
WITH sh : share, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, next:val
PRE [ ]
    PROP(
        writable_share sh /\
        ((isptr original_freelist_pointer /\ Nat.lt O n) \/ (* orginal list is a pointer to a list of size greater than 0 *)
            (original_freelist_pointer = nullval /\ Nat.eq O n)) /\ (* orginal freelist does not contain any list and therefore is a nullpointer *)
            is_pointer_or_null next 
    ) 
    PARAMS () GLOBALS(gv)
    SEP (   
            data_at sh (t_run) next original_freelist_pointer *
            freelistrep sh n original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
        (*data_at sh (t_run) next original_freelist_pointer;
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)*)) (* q can be nullval meaning that there is only one run *)
POST [ tptr tvoid ]
    PROP()
        RETURN (original_freelist_pointer) (* we return the head like in the pop function*)
        SEP (
            data_at sh (t_run) next original_freelist_pointer *
            freelistrep sh n original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
            (*if Nat.ltb O n then
                !! malloc_compatible (sizeof t_run) original_freelist_pointer &&  (* p is compatible with a memory block of size sizeof theader. *)
                data_at sh t_run next original_freelist_pointer *
                freelistrep sh (Nat.sub n (S O)) next *
                data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
            else 
                freelistrep sh n original_freelist_pointer *
                data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)*)

            (* data_at sh (t_run) next original_freelist_pointer;
            data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)*)
            ).

Definition client1_spec := (* kind of pop *)
DECLARE _client1
WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals, n : nat, next:val, number_structs_available:nat
PRE [ tptr tvoid ]
    PROP(
        writable_share sh /\
        is_pointer_or_null new_head /\
        is_pointer_or_null original_freelist_pointer /\
        (Nat.le (S O) number_structs_available)
    ) 
    PARAMS (new_head) GLOBALS(gv)
    SEP ( 
        freelistrep sh n original_freelist_pointer *
        available sh number_structs_available new_head PGSIZE *
        data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
    )
POST [ tptr tvoid ]
    PROP()
        RETURN (original_freelist_pointer) (* we return the head like in the pop function*)
        SEP (
            freelistrep sh n original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
            ).
            

(************************ Gprog  *************************)

Definition Gprog : funspecs := [
    kfree1_spec; 
    kalloc1_spec; 
    client1_spec
].

(************************ Proofs  *************************)
Lemma body_kfree1: semax_body Vprog Gprog f_kfree1 kfree1_spec.
Proof. start_function. Intros. destruct number_structs_available eqn:en; try rep_lia. destruct H. repeat forward. 
    entailer.
    induction n. 
    - assert (original_freelist_pointer = nullval). {
         rewrite <- H2; auto.
      }
      rewrite H11. unfold freelistrep. Exists nullval. fold available. 
      replace ((S n0) - 1)%nat with n0; try rep_lia.
      entailer!.
   - unfold freelistrep. Intros next_orig. Exists original_freelist_pointer. entailer.
      Exists next_orig. entailer. fold freelistrep. fold available. replace ((S n0) - 1)%nat with n0; try rep_lia. entailer!.
Qed.


Lemma body_kalloc1: semax_body Vprog Gprog f_kalloc1 kalloc1_spec.
Proof. start_function. forward. (*unfold abbreviate in POSTCONDITION.*)
forward_if (PROP ()
            LOCAL (temp _r original_freelist_pointer; 
                  temp _t'1 (if eq_dec original_freelist_pointer nullval 
                              then nullval else next); gvars gv)
            SEP (data_at sh t_run next original_freelist_pointer; 
               data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem))).
- forward. forward. entailer!. destruct (eq_dec original_freelist_pointer nullval); auto. subst. inversion H0.
- forward. entailer!. inversion H1. inversion H0. 
- destruct (eq_dec original_freelist_pointer nullval).
   + forward. 
   + forward. 
Qed.


(*Lemma body_kalloc1: semax_body Vprog Gprog f_kalloc1 kalloc1_spec.
Proof. start_function. destruct H; Intros. forward.
forward_if (
    PROP ( )
    LOCAL (temp _r original_freelist_pointer; 
            temp _t'1 (if eq_dec original_freelist_pointer nullval then nullval else next);
             gvars gv)
    SEP ( 
        if Nat.ltb O n then
            !! malloc_compatible (sizeof t_run) original_freelist_pointer &&  (* p is compatible with a memory block of size sizeof theader. *)
            data_at sh t_run next original_freelist_pointer *
            freelistrep sh (Nat.sub n (S O)) next *
            data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
        else 
            freelistrep sh n original_freelist_pointer *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) 
    )
).
- simpl in H0; destruct original_freelist_pointer eqn:eofl; auto_contradict.
    induction n.
    unfold freelistrep.
    + destruct H0; destruct H0 as [H2 H3].
        * inversion H3.
        * assert (False -> Vptr b i = nullval); intros; auto_contradict.
    + unfold freelistrep; fold freelistrep. Intros next0. admit.
- forward. destruct ((0 <? n)%nat) eqn:en.
    + entailer. destruct H0. 
        * destruct H0; auto_contradict.
        * destruct H0; unfold Nat.eq in H1. rewrite <- H1 in en; inversion en.
    + destruct H0; destruct H0.
        * unfold Nat.lt in H2. subst. auto_contradict.
        * entailer.


forward.*)

(*Lemma body_kalloc1: semax_body Vprog Gprog f_kalloc1 kalloc1_spec.
Proof. start_function. destruct H. Intros. forward. (*unfold abbreviate in POSTCONDITION.*)
forward_if (PROP ()
            LOCAL (temp _r original_freelist_pointer; 
                  temp _t'1 (if eq_dec original_freelist_pointer nullval 
                              then nullval else next); gvars gv)
            SEP ( if Nat.ltb O n then
                    !! malloc_compatible (sizeof t_run) original_freelist_pointer &&  (* p is compatible with a memory block of size sizeof theader. *)
                    data_at sh t_run next original_freelist_pointer *
                    freelistrep sh (Nat.sub n (S O)) next *
                    data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
                else 
                    freelistrep sh n original_freelist_pointer *
                    data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
)).
- admit. (*forward. forward. entailer!. destruct (eq_dec original_freelist_pointer nullval); auto. subst. inversion H0.*)
- forward. admit. (*entailer!. inversion H1. inversion H0. *) 
- destruct (eq_dec original_freelist_pointer nullval).
   + forward. 
   + forward. 
Admitted.*)

Lemma body_client1: semax_body Vprog Gprog f_client1 client1_spec.
Proof.
start_function.
forward_call (sh, new_head, original_freelist_pointer, xx, gv, n, PGSIZE, number_structs_available). (* call kfree1 *)
- destruct H as [H1 [H2 [H3 H4]]]; split; auto.
- forward_call (sh, new_head, xx, gv, S n, next). (* call kalloc1 *)
    + entailer!.
    + destruct H as [H1 [H2 [H3 H4]]]; split; auto.
    + (*unfold abbreviate in POSTCONDITION.*) forward. destruct (0 <? (S n))%nat eqn:en; auto_contradict.
    admit.
Admitted.
