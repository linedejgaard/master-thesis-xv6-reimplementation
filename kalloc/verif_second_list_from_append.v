Require Import VST.floyd.proofauto.
Require Import VC.second_list.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_node := Tstruct _node noattr.

(************************ list rep *************************)

Fixpoint listrep (sh: share) (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_node (h, y) x * listrep sh hs y
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


Lemma listrep_null: forall sh contents,
    listrep sh contents nullval = !! (contents=nil) && emp.
Proof.
destruct contents; unfold listrep; fold listrep.
autorewrite with norm. auto.
apply pred_ext.
Intros y. entailer. destruct H; contradiction.
Intros. discriminate.
Qed.

Lemma listrep_nonnull: forall contents sh x,
  x <> nullval ->
  listrep sh contents x =
    EX h: val, EX hs: list val, EX y:val,
      !! (contents = h :: hs) && data_at sh t_node (h, y) x * listrep sh hs y.
Proof.
(** Again, [pred_ext] will be useful here. *)
  intros; apply pred_ext.
  - destruct contents.
    + unfold listrep. entailer!. 
    + unfold listrep; fold listrep. Intros y. Exists v contents y. entailer!. 
  - Intros h hs y. rewrite H0. unfold listrep at 2; fold listrep. Exists y. entailer!.
Qed.


(*Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.*)

(** Spec *)

Definition add_spec :=
 DECLARE _add
  WITH sh : share, x: val, y: val, s1: list val, s2: list val
  PRE [ tptr t_node , tptr t_node]
     PROP(writable_share sh; x <> nullval; y <> nullval; length s1 = (Z.to_nat (Int.unsigned (Int.repr 1)))) (* not sure this is ok to say *)
     PARAMS (x; y) GLOBALS()
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_node ]
    EX r: val,
     PROP()
     RETURN (r)
     SEP (listrep sh (s1++s2) r).

Definition Gprog : funspecs :=   ltac:(with_library prog [ add_spec ]).

Module Proof1.

Definition lseg (sh: share) (contents: list val) (x z: val) : mpred :=
  ALL cts2:list val, listrep sh cts2 z -* listrep sh (contents++cts2) x.

Lemma body_add: semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
forward_if. (* if head *)
- forward. (* head == nullval, which is not possible by assumption.. *)
- rewrite (listrep_nonnull _ _ x) by auto. 
   Intros h hs y0. 
   forward_if; try forward.
   forward. simpl. Exists x. entailer!. unfold listrep; fold listrep. Exists y.
   entailer!. 
   destruct hs.
   + simpl. unfold listrep. entailer!!.
   + inversion H1. 
Qed.

(** compiles until this..*)
   
