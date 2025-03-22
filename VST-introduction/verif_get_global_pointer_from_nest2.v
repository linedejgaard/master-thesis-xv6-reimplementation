Require Import VST.floyd.proofauto.
Require Import VC.get_global_pointer.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_run := Tstruct _run noattr.

(************************ list rep  *************************)

Fixpoint listrep (sh: share) (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_run (y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.

   (*
   The lemma states that for any list sigma and any pointer p, if listrep sigma p holds, then:
      p is either a valid pointer or null.
      p is null if and only if sigma is an empty list (nil).
   *)
Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; 
  unfold listrep; fold listrep; intros. entailer!. intuition.
Intros y. entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sh contents p,
   sepalg.nonidentity sh ->
   listrep sh contents p |-- valid_pointer p.
Proof.
 destruct contents; unfold listrep; fold listrep; intros; Intros; subst.
 auto with valid_pointer.
 Intros y.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto.
 simpl;  computable.
Qed.

#[export] Hint Resolve listrep_valid_pointer : valid_pointer.


Definition get_freelist1_input_spec :=
 DECLARE _get_freelist1_input
       WITH sh: share, sigma : list val, p: val
       PRE  [ tptr t_run ]
       PROP ()
       PARAMS (p)
       SEP (listrep sh sigma p)
       POST [ (tptr t_run) ]
       PROP () RETURN (p)
       SEP (listrep sh sigma p).

(************************ freelist rep  *************************)
Fixpoint freelistrep (sh: share) (n: nat) (p: val) : mpred :=
 match n with
 | S n' => EX next: val, 
        !! malloc_compatible (sizeof t_run) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        data_at sh t_run next p * (* at the location p, there is a t_run structure with the value next *)
        freelistrep sh n' next (* "*" ensures no loops... *)
 | O => !! (p = nullval) && emp
 end.


Arguments freelistrep sh n p : simpl never.

Lemma freelistrep_local_prop: forall sh n p, 
   freelistrep sh n p |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros.
  induction n as [| n' IH].
  - unfold freelistrep. entailer!. split; auto.
    + split; auto.
    + split; try lia. intros. simpl in *. inversion H.
  - unfold freelistrep. destruct p; Intro y; entailer!. split.
    + split; intros; inversion H2.
    + split; intros; auto. try lia. 
   Qed.
#[export] Hint Resolve freelistrep_local_prop : saturate_local.


Lemma freelistrep_valid_pointer:
  forall sh n p, 
  readable_share sh ->
   freelistrep Ews n p |-- valid_pointer p.
Proof.
  intros. destruct n.
  - unfold freelistrep. entailer!.
  - unfold freelistrep. Intro y; entailer.
Qed. 
#[export] Hint Resolve freelistrep_valid_pointer : valid_pointer.


Lemma freelistrep_null: forall sh n x,
       x = nullval ->
       freelistrep sh n x = !! (n = O) && emp.
Proof.
   intros.
   destruct n; unfold freelistrep; fold freelistrep.
   autorewrite with norm. auto.
   apply pred_ext.
   Intros y. entailer. 
   destruct n; entailer!; try discriminate H0. 
Qed.


Lemma freelistrep_nonnull: forall n sh x,
   x <> nullval ->
   freelistrep sh n x =
   EX m : nat, EX next:val,
          !! (n = S m) && !! malloc_compatible (sizeof t_run) x && data_at sh t_run next x * freelistrep sh m next.
Proof.
   intros; apply pred_ext.
   - destruct n. 
         + unfold freelistrep. entailer!.
         + unfold freelistrep; fold freelistrep. Intros y.
         Exists n y. entailer!.
   - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. Exists y. entailer!.
Qed.

Definition get_freelist1_input_spec' :=
DECLARE _get_freelist1_input
       WITH sh: share, n : nat, p: val
       PRE  [ tptr t_run ]
       PROP ()
       PARAMS (p)
       SEP (freelistrep sh n p)
       POST [ (tptr t_run) ]
       PROP () RETURN (p)
       SEP (freelistrep sh n p).

(************************ get i global *************************)
Definition t_i := Tstruct _run noattr.

Definition get_i_spec := (* only works for Ews*)
 DECLARE _get_i
  WITH v:Z, sh:share, gv: globals
  PRE [  ]
          PROP  (readable_share sh)
          PARAMS() GLOBALS (gv)
          SEP   (data_at sh tint (Vint (Int.repr v)) (gv _i))
  POST [ tint ]
        PROP () RETURN (Vint (Int.repr v))
           SEP (data_at sh tint (Vint (Int.repr v)) (gv _i)).     
       
(************************ freelist rep global *************************)

Definition get_freelist1_spec :=
 DECLARE _get_freelist1
       WITH b:block, p: ptrofs, sh: share, gv: globals
       PRE  [ ]
       PROP (readable_share sh)
       PARAMS () GLOBALS (gv)
       SEP (data_at sh (tptr t_run) (Vptr b p) (gv _freelist1)) (* what _freelist stores is a pointer *)
       POST [ (tptr t_run) ]
       PROP () RETURN (Vptr b p)
       SEP (data_at sh (tptr t_run) (Vptr b p) (gv _freelist1)).


(************************ get freelist global *************************)
Definition t_struct_kmem := Tstruct _struct_kmem noattr.

Definition get_xx_spec :=
 DECLARE _get_xx
  WITH sh: share, v : reptype' t_struct_kmem, gv: globals
  PRE  []
        PROP (readable_share sh)
        PARAMS() GLOBALS (gv)
        SEP(data_at sh t_struct_kmem (repinj _ v) (gv _kmem))
  POST [ tint ]
         PROP()
         RETURN (Vint (fst v))
         SEP (data_at sh t_struct_kmem (repinj _ v) (gv _kmem)).

Definition get_freelist_spec :=
DECLARE _get_freelist
       WITH sh: share, b:block, p: ptrofs, xx : Z , gv: globals
       PRE  []
       PROP (readable_share sh)
       PARAMS() GLOBALS (gv)
       SEP(data_at sh t_struct_kmem (Vint (Int.repr xx), Vptr b p) (gv _kmem))
       POST [ tptr t_run ]
              PROP()
              RETURN (Vptr b p)
              SEP (data_at sh t_struct_kmem (Vint (Int.repr xx), Vptr b p) (gv _kmem)).
              

(************************ free listrep non_global *************************)

Definition free_spec := (** uses listrep_cons*)
 DECLARE _free
   WITH sh : share, q: val, il: list val, n:val
   PRE [ tptr tvoid , tptr t_run]
      PROP(writable_share sh) (* not sure this is ok to say *)
      PARAMS (n; q) GLOBALS()
      SEP (data_at sh (t_run) nullval n; listrep sh il q)
   POST [ tvoid ]
      PROP()
      RETURN () (* no return value *)
      SEP (data_at sh (t_run) q n;  listrep sh il q).

(************************ free freelistrep non_global *************************)

Definition free_spec' := 
 DECLARE _free
   WITH sh : share, q: val, n:nat, f:val
   PRE [ tptr tvoid , tptr t_run]
      PROP(writable_share sh) (* not sure this is ok to say *)
      PARAMS (f; q) GLOBALS()
      SEP (data_at sh (t_run) nullval f; freelistrep sh n q)
   POST [ tvoid ]
      PROP()
      RETURN () (* no return value *)
      SEP (data_at sh (t_run) q f;  freelistrep sh n q).     
       

(************************ kfree1 freelistrep global *************************)

Definition kfree1_spec := 
 DECLARE _kfree1
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
(* I THINK THIS IS WRONG, BECAUSE I DON'T THEY THEY ARE DISJOINT: *)
Definition kfree1_1_spec := 
 DECLARE _kfree1
   WITH sh : share, new_head:val, original_freelist_pointer:val, xx:Z, gv:globals
   PRE [ tptr tvoid]
      PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) (* writable_share is necessary *)
      PARAMS (new_head) GLOBALS(gv)
      SEP (data_at sh (t_run) nullval new_head * (* the input run struct should exists *)
      data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* the kmem freelist should exists, xx is a placeholder for the spinlock *)
      )
   POST [ tvoid ]
      PROP()
      RETURN () (* no return value *)
      SEP (
         data_at sh (t_run) (original_freelist_pointer) new_head * (* the new head should point to the original freelist pointer *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem) (** the top of the freelist should point to the new head *)
         ).   

(************************ alloc non_global *************************)

Definition alloc_spec := (* assume the list isn't empty *)
 DECLARE _alloc
   WITH sh : share, q: val, il: list val, n:val            
   PRE [ tptr t_run]
      PROP(writable_share sh)
      PARAMS (n) GLOBALS()
      SEP (data_at sh (t_run) q n; listrep sh il q) (* q can be nullval meaning that there is only one run *)
   POST [ tptr tvoid ]
      PROP()
      RETURN (n) (* we return the head like in the pop function*)
      SEP (data_at sh (t_run) q n; listrep sh il q). (** I AM NOT SURE THE GARBAGE COLLECTION TAKES THE HEAD?*)

Definition alloc_spec' := (* this doesn't assume that the list is empty, but that q is either a pointer or a nullval *)
 DECLARE _alloc
   WITH sh : share, q: val, il: list val, n:val            
   PRE [ tptr t_run ]
      PROP(writable_share sh; is_pointer_or_null q) 
      PARAMS (n) GLOBALS()
      SEP (data_at sh (t_run) q n) (* q can be nullval meaning that there is only one run *)
   POST [ tptr tvoid ]
      PROP()
      RETURN (n) (* we return the head like in the pop function*)
      SEP (data_at sh (t_run) q n). (** I THINK THE HEAD IS STILL IN MEMORY, I AM NOT SURE WE CAN SAY SOMETHING ABOUT THE REST OF THE LIST *)


(************************ alloc global *************************)
Definition kalloc1_spec := (* this doesn't assume that the list is empty, but that q is either a pointer or a nullval *)
 DECLARE _kalloc1
   WITH sh : share, original_freelist_pointer:val, xx:Z, next:val, gv:globals
   PRE [ ]
      PROP(writable_share sh; is_pointer_or_null next) 
      PARAMS () GLOBALS(gv)
      SEP ( data_at sh (t_run) next original_freelist_pointer;
         data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)) (* q can be nullval meaning that there is only one run *)
   POST [ tptr tvoid ]
      PROP()
      RETURN (original_freelist_pointer) (* we return the head like in the pop function*)
      SEP (
         data_at sh (t_run) next original_freelist_pointer;
         data_at sh t_struct_kmem (Vint (Int.repr xx), next) (gv _kmem)
         ).


(************************ pointer comparison *************************)
Definition pointer_compare_0_spec :=
 DECLARE _pointer_compare_0
  WITH p: val, q:val, sh: share, p_value:int, q_value:int
  PRE  [ tptr tint, tptr tint]
        PROP (sepalg.nonidentity sh)
        PARAMS (p; q)
        SEP(data_at sh tint (Vint p_value) p; data_at sh tint (Vint q_value) q)
  POST [ tint ]
         PROP()
         RETURN (Vint (if eq_dec p q then Int.one else Int.zero))
         SEP (data_at sh tint (Vint p_value) p; data_at sh tint (Vint q_value) q).

Definition pointer_compare_1_spec :=
   DECLARE _pointer_compare_1
      WITH p: val, q:val, sh: share, p_value:int, q_value:int
      PRE  [ tptr tschar, tptr tschar]
            PROP (sepalg.nonidentity sh)
            PARAMS (p; q)
            SEP(data_at sh tint (Vint p_value) p; data_at sh tint (Vint q_value) q)
      POST [ tint ]
            PROP()
            RETURN (Vint (if eq_dec p q then Int.one else Int.zero))
            SEP (data_at sh tint (Vint p_value) p; data_at sh tint (Vint q_value) q).

(*Definition pointer_le_bool (pa_start pa_end : val) : bool :=
   let comparison_result := 
   force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp Cle pa_start pa_end))) in
   match comparison_result with
   | Vint z =>
      if Z.eqb (Int.signed z) 1 then true
      else if Z.eqb (Int.signed z) 0 then false
      else false (* or you could raise an error, or have another default if the result is unexpected *)
   | _ => false (* Or raise an error, or have another default if the result is unexpected *)
   end.*)

Definition pointer_le_bool (p q : val) : bool :=
   eq_dec (force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp Cle p q)))) (Vint (Int.repr 1)).
            
Definition pointer_compare_2_spec :=
   DECLARE _pointer_compare_2
      WITH p: val, q:val, p_value:int, q_value:int, sh: share
      PRE  [ tptr tint, tptr tint]
            PROP (sepalg.nonidentity sh) (* not sure this is correct..*)
            PARAMS (p; q)
            SEP(denote_tc_test_order p q) 
      POST [ tint ]
            PROP()
            RETURN (force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp Cle p q))))
            SEP (denote_tc_test_order p q). 

Check force_val.
Check sem_cmp_pp.
Print sem_cmp_pp.
Print bool2val.

Definition pointer_compare_3_spec :=
   DECLARE _pointer_compare_3
      WITH p: val, q:val, p_value:int, q_value:int, sh: share
      PRE  [ tptr tint, tptr tint]
            PROP (sepalg.nonidentity sh) (* not sure this is correct..*)
            PARAMS (p; q)
            SEP( denote_tc_test_order p q) 
      POST [ tint ]
            PROP()
            RETURN (if (pointer_le_bool p q) 
                     then Vint (Int.repr (42))
                     else Vint (Int.repr (13))
                     )
            SEP (denote_tc_test_order p q). 
                       

(************************ calls kfree1 *************************)

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
         PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) (* writable_share is necessary *)
         PARAMS (new_head) GLOBALS(gv)
         SEP (data_at sh (t_run) nullval new_head; (* the input run struct should exists *)
         data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* the kmem freelist should exists, xx is a placeholder for the spinlock *)
         )
      POST [ tvoid ]
         PROP()
         RETURN () (* no return value *)
         SEP (
            if (eq_dec new_head nullval) then
            data_at sh (t_run) nullval new_head * (* the input run struct should exists *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* the kmem freelist should exists, xx is a placeholder for the spinlock *)
            else 
            data_at sh (t_run) (original_freelist_pointer) new_head *(* the new head should point to the original freelist pointer *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem) (** the top of the freelist should point to the new head *)
            ).

Definition freerange_no_loop_no_add_spec := 
   DECLARE _freerange_no_loop_no_add
      WITH sh : share, new_head:val, pa_end:val, original_freelist_pointer:val, xx:Z, gv:globals
      PRE [ tptr tvoid, tptr tvoid]
         PROP(writable_share sh; is_pointer_or_null original_freelist_pointer) 
         PARAMS (new_head; pa_end) GLOBALS(gv)
         SEP (
            denote_tc_test_order new_head pa_end *
            data_at sh (t_run) nullval new_head *
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem)
         )
      POST [ tvoid ]
         PROP()
         RETURN () (* no return value *)
         SEP (
            if (eq_dec (force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp Cle new_head pa_end)))) (Vint (Int.repr 1))) 
            then
            (data_at sh (t_run) nullval new_head * (* the input run struct should exists *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem) (* the kmem freelist should exists, xx is a placeholder for the spinlock *)
            ) else 
            (data_at sh (t_run) (original_freelist_pointer) new_head *(* the new head should point to the original freelist pointer *)
            data_at sh t_struct_kmem (Vint (Int.repr xx), new_head) (gv _kmem) (** the top of the freelist should point to the new head *)
         )).

(************************ rounding *************************)

Definition PGSIZE : Z := 4096. (** I think we should be able to retrieve this.. but it has to be greater than 0 *)

(* PGROUNDUP function in Coq *)
Definition PGROUNDUP (sz : Z) : Z :=
  ((sz + PGSIZE - 1) / PGSIZE) * PGSIZE.

Definition min_size : Z := 1.

Definition align_pointer_spec := (* assume the list isn't empty *)
 DECLARE _align_pointer
   WITH sh : share, b:block, p:ptrofs        
   PRE [ tptr tvoid]
      PROP(sepalg.nonidentity sh)
      PARAMS (Vptr b p) GLOBALS()
      SEP (memory_block sh min_size (Vptr b p)) (* q can be nullval meaning that there is only one run *)
   POST [ tvoid ]
      PROP()
      RETURN (Vptr b p) (* we return the head like in the pop function*)
      SEP (memory_block sh min_size (Vptr b p)). (** I AM NOT SURE THE GARBAGE COLLECTION TAKES THE HEAD?*)




(************************************)
Definition Gprog : funspecs := [get_freelist1_input_spec; 
get_freelist1_input_spec'; get_freelist1_spec; get_i_spec; 
get_xx_spec; get_freelist_spec;
free_spec; free_spec'; alloc_spec; alloc_spec'; 
kfree1_spec; kfree1_1_spec;
kalloc1_spec; call_kfree1_spec; 
call_kfree1_if_1_spec; pointer_compare_0_spec; pointer_compare_1_spec; 
pointer_compare_2_spec; 
pointer_compare_3_spec; 
freerange_no_loop_no_add_spec; align_pointer_spec].


Lemma body_get_freelist_input_spec:  semax_body Vprog Gprog f_get_freelist1_input get_freelist1_input_spec.
Proof. start_function. forward. Qed.

Lemma body_get_freelist_input_spec':  semax_body Vprog Gprog f_get_freelist1_input get_freelist1_input_spec'.
Proof. start_function. forward. Qed.

Lemma body_get_i_spec: semax_body Vprog Gprog f_get_i get_i_spec.
Proof. start_function. repeat forward. Qed.

Lemma body_get_freelist1: semax_body Vprog Gprog f_get_freelist1 get_freelist1_spec.
Proof. start_function. repeat forward. Qed.

Lemma body_get_xx : semax_body Vprog Gprog f_get_xx get_xx_spec.
Proof. start_function. simpl in v. unfold_repinj. repeat forward. Qed.

Lemma body_get_freelist : semax_body Vprog Gprog f_get_freelist get_freelist_spec.
Proof. start_function. forward. forward. Qed.

Lemma body_free: semax_body Vprog Gprog f_free free_spec.
Proof. start_function. repeat forward. entailer!. Qed.

Lemma body_free': semax_body Vprog Gprog f_free free_spec'.
Proof. start_function. repeat forward. entailer!. Qed.

Lemma body_kfree1: semax_body Vprog Gprog f_kfree1 kfree1_spec.
Proof. start_function. repeat forward. entailer!. Qed.

Lemma body_kfree1_1: semax_body Vprog Gprog f_kfree1 kfree1_1_spec.
Proof. start_function. Intros. repeat forward. entailer!. Qed.

Lemma body_alloc: semax_body Vprog Gprog f_alloc alloc_spec.
Proof.
start_function. forward. 
forward_if (PROP () LOCAL (temp _lst (if eq_dec n nullval then nullval else q);
                            temp _head n)
                 SEP (data_at sh t_run q n; listrep sh il q)).
- forward. entailer!. destruct (eq_dec n nullval); auto. subst. inversion H.
- forward. entailer!.
- forward.
Qed.

Lemma body_alloc': semax_body Vprog Gprog f_alloc alloc_spec'.
Proof.
start_function. forward. 
forward_if (PROP () LOCAL (temp _lst (if eq_dec n nullval then nullval else q);
                            temp _head n)
                 SEP (data_at sh t_run q n)).
- forward. entailer!. destruct (eq_dec n nullval); auto. subst. inversion H0. 
- forward. entailer!.
- forward.
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

Lemma body_call_kfree1: semax_body Vprog Gprog f_call_kfree1 call_kfree1_spec.
Proof.
start_function.
forward_call.
entailer!.
Qed.

Lemma body_call_kfree1_if_1_spec: semax_body Vprog Gprog f_call_kfree1_if_1 call_kfree1_if_1_spec.
Proof.
start_function.
forward_if.
- forward_call.
  entailer!.
  destruct (eq_dec new_head nullval); entailer!.
- forward. entailer!. destruct (eq_dec nullval nullval); entailer!.
Qed.

Lemma body_pointer_compare_0: semax_body Vprog Gprog f_pointer_compare_0 pointer_compare_0_spec.
Proof. start_function. forward. Qed.

Lemma body_pointer_compare_1: semax_body Vprog Gprog f_pointer_compare_1 pointer_compare_1_spec.
Proof. start_function. forward. Qed.

Lemma body_pointer_compare_2: semax_body Vprog Gprog f_pointer_compare_2 pointer_compare_2_spec.
Proof. start_function. forward. Qed.

Lemma cmp_is_either_0_or_1 : forall p q i,
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

Lemma body_pointer_compare_3: semax_body Vprog Gprog f_pointer_compare_3 pointer_compare_3_spec.
Proof. start_function. forward_if.
- forward.
   unfold pointer_le_bool.    
   destruct (eq_dec (force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp Cle p q))))
   (Vint (Int.repr 1))); entailer!.
   destruct (sem_cmp_pp Cle p q) eqn:e; try discriminate.
   destruct v; try discriminate.
   simpl in *. apply typed_true_tint_Vint in H.
   destruct (eq_dec (i) ((Int.zero))); try contradiction.
   apply cmp_is_either_0_or_1 in e. destruct e; subst; try contradiction.
- forward.
   unfold pointer_le_bool. 
   destruct (eq_dec (force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp Cle p q))))
   (Vint (Int.repr 1))); entailer!.
   destruct (sem_cmp_pp Cle p q) eqn:eCmp; try discriminate.
   destruct v; try discriminate.
   simpl in *. apply typed_false_tint_Vint in H.
   rewrite H in e. inversion e.
Qed.

Lemma body_freerange_no_loop_no_add: semax_body Vprog Gprog f_freerange_no_loop_no_add freerange_no_loop_no_add_spec.
Proof. start_function. forward_if. entailer!.
Admitted.


(*Lemma body_align_pointer: semax_body Vprog Gprog f_align_pointer align_pointer_spec.
Proof. start_function. forward. Admitted.*)

(*** stop""*)



    


