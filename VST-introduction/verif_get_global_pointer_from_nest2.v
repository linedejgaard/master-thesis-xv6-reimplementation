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
        freelistrep sh n' next
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
       WITH b:block, p: ptrofs, sh: share, n : nat, gv: globals
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
              

(************************ free freelist non_global *************************)

Definition free_spec := (** uses listrep_cons*)
 DECLARE _free
   WITH sh : share, p: val, q: val, il: list val, n:val
   PRE [ tptr tvoid , tptr t_run]
      PROP(writable_share sh) (* not sure this is ok to say *)
      PARAMS (n; q) GLOBALS()
      SEP (data_at sh (t_run) nullval n; listrep sh il q)
   POST [ tvoid ]
      PROP()
      RETURN () (* no return value *)
      SEP (data_at sh (t_run) q n;  listrep sh il q).




(************************************)
Definition Gprog : funspecs := [get_freelist1_input_spec; get_freelist1_input_spec'; get_freelist1_spec; get_i_spec; get_xx_spec; get_freelist_spec].


Lemma body_get_freelist_input_spec:  semax_body Vprog Gprog f_get_freelist1_input get_freelist1_input_spec.
Proof. start_function. forward. Qed.

Lemma body_get_freelist_input_spec':  semax_body Vprog Gprog f_get_freelist1_input get_freelist1_input_spec'.
Proof. start_function. forward. Qed.

Lemma body_get_i_spec: semax_body Vprog Gprog f_get_i get_i_spec.
Proof. 
start_function. repeat forward. Qed.

Lemma body_get_freelist1: semax_body Vprog Gprog f_get_freelist1 get_freelist1_spec.
Proof. start_function. repeat forward. Qed.

Lemma body_get_xx : semax_body Vprog Gprog f_get_xx get_xx_spec.
Proof. start_function. simpl in v. unfold_repinj. repeat forward. Qed.

Lemma body_get_freelist : semax_body Vprog Gprog f_get_freelist get_freelist_spec.
Proof. start_function. forward. forward. Qed.

Lemma body_free: semax_body Vprog Gprog f_free free_spec.
Proof. start_function. repeat forward. entailer!. Qed.


