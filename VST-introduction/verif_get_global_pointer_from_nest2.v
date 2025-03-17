Require Import VST.floyd.proofauto.
Require Import VC.get_global_pointer.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_node := Tstruct _node noattr.

(************************ list rep  *************************)

Fixpoint listrep (sh: share) (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_node (y) x * listrep sh hs y
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


Definition get_freelist_input_spec :=
 DECLARE _get_freelist_input
       WITH sh: share, sigma : list val, p: val
       PRE  [ tptr t_node ]
       PROP ()
       PARAMS (p)
       SEP (listrep sh sigma p)
       POST [ (tptr t_node) ]
       PROP () RETURN (p)
       SEP (listrep sh sigma p).

(************************ freelist rep  *************************)
Fixpoint freelistrep (sh: share) (n: nat) (p: val) : mpred :=
 match n with
 | S n' => EX next: val, 
        !! malloc_compatible (sizeof t_node) p &&  (* p is compatible with a memory block of size sizeof theader. *)
        data_at sh t_node next p * (* at the location p, there is a t_node structure with the value next *)
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
          !! (n = S m) && !! malloc_compatible (sizeof t_node) x && data_at sh t_node next x * freelistrep sh m next.
   Proof.
       intros; apply pred_ext.
       - destruct n. 
              + unfold freelistrep. entailer!.
              + unfold freelistrep; fold freelistrep. Intros y.
              Exists n y. entailer!.
       - Intros m y. rewrite H0. unfold freelistrep at 2; fold freelistrep. Exists y. entailer!.
Qed.

Definition get_freelist_input_spec' :=
DECLARE _get_freelist_input
       WITH sh: share, n : nat, p: val
       PRE  [ tptr t_node ]
       PROP ()
       PARAMS (p)
       SEP (freelistrep sh n p)
       POST [ (tptr t_node) ]
       PROP () RETURN (p)
       SEP (freelistrep sh n p).

(************************ get i global *************************)
Definition t_i := Tstruct _node noattr.

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
       SEP (data_at sh (tptr t_node) (Vptr b p) (gv _freelist)) (* what _freelist stores is a pointer *)
       POST [ (tptr t_node) ]
       PROP () RETURN (Vptr b p)
       SEP (data_at sh (tptr t_node) (Vptr b p) (gv _freelist)).

(*Definition get_freelist1_spec' :=
 DECLARE _get_freelist1
       WITH sh: share, n : nat, gv: globals
       PRE  [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (freelistrep sh n (gv _freelist))
       POST [ (tptr t_node) ]
       PROP () RETURN (gv _freelist)
       SEP (freelistrep sh n (gv _freelist)).*)

(************************ get innerlist global *************************)
Definition t_struct_b := Tstruct _b noattr.

Definition get_spec :=
 DECLARE _get
  WITH sh: share, v : reptype' t_struct_b, gv: globals
  PRE  []
        PROP (readable_share sh)
        PARAMS() GLOBALS (gv)
        SEP(data_at sh t_struct_b (repinj _ v) (gv _p))
  POST [ tint ]
         PROP()
         RETURN (Vint (fst v))
         SEP (data_at sh t_struct_b (repinj _ v) (gv _p)).



(************************************)
Definition Gprog : funspecs := [get_freelist_input_spec; get_freelist_input_spec'; get_freelist1_spec; get_i_spec; get_spec].


Lemma body_get_freelist_input_spec:  semax_body Vprog Gprog f_get_freelist_input get_freelist_input_spec.
Proof. start_function. forward. Qed.

Lemma body_get_freelist_input_spec':  semax_body Vprog Gprog f_get_freelist_input get_freelist_input_spec'.
Proof. start_function. forward. Qed.

Lemma body_get_i_spec: semax_body Vprog Gprog f_get_i get_i_spec.
Proof. 
start_function. repeat forward. Qed.

Lemma body_get_freelist1: semax_body Vprog Gprog f_get_freelist1 get_freelist1_spec.
Proof. start_function. repeat forward. Qed.

Lemma body_get : semax_body Vprog Gprog f_get get_spec.
Proof. start_function. simpl in v. unfold_repinj. repeat forward. Qed.

(*
Lemma body_get_xx : semax_body Vprog Gprog f_get_xx get_xx_spec.
Proof. start_function. 
simpl in v.
unfold_repinj. forward.


Lemma body_get_innerlist: semax_body Vprog Gprog f_get_innerlist get_innerlist_spec.
Proof. start_function. forward. Qed.*)