Require Import VST.floyd.proofauto.
Require Import VC.second_list_v2.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_node := Tstruct _node noattr.

(************************ list rep *************************)

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
      !! (contents = h :: hs) && data_at sh t_node (y) x * listrep sh hs y.
Proof.
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


(************************)
(************************)
(*Definition listrep_cons sh (il: list val) (p: val) :=
 EX q: val,
  data_at Ews (t_node) q p * (** don't know if it should be ews here.. *)
  listrep sh il q.

Arguments listrep_cons sh il p : simpl never.

Lemma listrep_cons_local_prop: forall il sh p, listrep_cons sh il p |--  !! (isptr p).
Proof.
  intros. destruct il; unfold listrep_cons; Intros q; entailer!. 
Qed.

#[export] Hint Resolve listrep_cons_local_prop : saturate_local.

Lemma listrep_cons_valid_pointer:
  forall sh il p,
  listrep_cons sh il p |-- valid_pointer p.
Proof.
  intros.  destruct il; unfold listrep_cons; Intros q; entailer!.
Qed. 
#[export] Hint Resolve listrep_cons_valid_pointer : valid_pointer.*)

(************************)
(************************)


(** Spec *)

Definition add_spec := (** uses listrep*)
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

Definition add_spec' := (** uses listrep_cons*)
 DECLARE _add
  WITH sh : share, p: val, q: val, il: list val, n:val
  PRE [ tptr t_node , tptr t_node]
     PROP(writable_share sh) (* not sure this is ok to say *)
     PARAMS (n; q) GLOBALS()
     SEP (data_at sh (t_node) nullval n; listrep sh il q)
  POST [ tptr t_node ]
    EX r: val,
     PROP()
     RETURN (r)
     SEP (data_at sh (t_node) q n;  listrep sh il q).
     

Definition add_void_spec :=
 DECLARE _add
  WITH sh : share, x: val, y: val, s1: list val, s2: list val
  PRE [ tptr tvoid , tptr t_node]
     PROP(writable_share sh; x <> nullval; y <> nullval; length s1 = (Z.to_nat (Int.unsigned (Int.repr 1)))) (* not sure this is ok to say *)
     PARAMS (x; y) GLOBALS()
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_node ]
    EX r: val,
     PROP()
     RETURN (r)
     SEP (listrep sh (s1++s2) r).


Definition add_void_spec' := (** uses listrep_cons*)
   DECLARE _add
   WITH sh : share, p: val, q: val, il: list val, n:val
   PRE [ tptr tvoid , tptr t_node]
      PROP(writable_share sh) (* not sure this is ok to say *)
      PARAMS (n; q) GLOBALS()
      SEP (data_at sh (t_node) nullval n; listrep sh il q)
   POST [ tptr t_node ]
      PROP()
      RETURN (if eq_dec q nullval then nullval else n) (* returns 0 when there is no tail, and head otherwise, so n *)
      SEP (data_at sh (t_node) q n;  listrep sh il q).


Definition free_spec := (** uses listrep_cons*)
   DECLARE _free
   WITH sh : share, p: val, q: val, il: list val, n:val
   PRE [ tptr tvoid , tptr t_node]
      PROP(writable_share sh) (* not sure this is ok to say *)
      PARAMS (n; q) GLOBALS()
      SEP (data_at sh (t_node) nullval n; listrep sh il q)
   POST [ tvoid ]
      PROP()
      RETURN () (* no return value *)
      SEP (data_at sh (t_node) q n;  listrep sh il q).

(*Definition remove_spec :=
DECLARE _remove
   WITH sh : share, x: val, s:val, ss: list val
   PRE [ tptr t_node]
      PROP(writable_share sh; x <> nullval) (* not sure this is ok to say *)
      PARAMS (x) GLOBALS()
      SEP (listrep_cons sh (s::ss) x)
   POST [ tptr t_node ]
   EX r:val,
      PROP()
      RETURN (r)
      SEP (listrep_cons sh ss r).*)

   
(*Definition remove_spec' := (* uses listrep_cons*)
   DECLARE _remove
      WITH sh : share, p: val, i: Z, il: list val 
      PRE [ tptr t_node]
         PROP(writable_share sh) (* not sure this is ok to say *)
         PARAMS (p) GLOBALS()
         SEP (data_at sh (t_node) q n; listrep sh il q)
      POST [ tptr t_node ]
      EX r:val,
         PROP()
         RETURN (r)
         SEP (listrep_cons sh il r).


         Definition pop_spec : ident * funspec :=
            DECLARE _pop
            WITH p: val, i: Z, il: list Z, gv: globals
            PRE [ tptr (Tstruct _stack noattr) ] 
               PROP () 
               PARAMS (p) GLOBALS(gv) 
               SEP (stack (i::il) p; mem_mgr gv)
            POST [ tint ] 
               PROP ( ) RETURN (Vint (Int.repr i)) SEP (stack il p; mem_mgr gv).
           
*)
(*Definition add_kmem_spec :=
DECLARE _add
   WITH sh : share, x: val, y: val, s1: list val, s2: list val, gv: globals
   PRE [ tptr tvoid]
      PROP(writable_share sh; x <> nullval; y <> nullval; length s1 = (Z.to_nat (Int.unsigned (Int.repr 1)))) (* not sure this is ok to say *)
      PARAMS (x) GLOBALS(gv)
      SEP (listrep sh s1 x; listrep sh s2 y)
   POST [ tptr t_node ]
   EX r: val,
      PROP()
      RETURN (r)
      SEP (listrep sh (s1++s2) r).
*)
Definition Gprog := [add_spec; add_spec'; add_void_spec; add_void_spec'; free_spec].
(*Definition Gprog := [add_spec; add_void_spec; remove_spec].*)

(*Definition lseg (sh: share) (contents: list val) (x z: val) : mpred :=
  ALL cts2:list val, listrep sh cts2 z -* listrep sh (contents++cts2) x.*)






Lemma body_add: semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
forward_if. (* if head *)
- forward. (* head == nullval, which is not possible by assumption.. *)
- rewrite (listrep_nonnull _ _ x) by auto. 
   Intros h hs y0.
   forward_if.
   forward
   forward.
   forward.
   forward.
   Exists x. simpl. unfold listrep; fold listrep. entailer!. Exists y. entailer!.
   destruct hs.
   + simpl. unfold listrep; entailer!.
   + inversion H1. 
Qed.

Lemma body_add': semax_body Vprog Gprog f_add add_spec'.
Proof.
start_function.
forward_if. (* if head *)
- forward. EExists. entailer!. (* head == nullval, which is not possible by assumption.. *)
- forward_if.
   +forward. EExists. entailer!.
   +forward.
   forward. Exists n. entailer!.
Qed.

Lemma body_add_void: semax_body Vprog Gprog f_add_void add_void_spec.
Proof.
start_function.
forward_if. (* if head *)
- forward. (* head == nullval, which is not possible by assumption.. *)
- rewrite (listrep_nonnull _ _ x) by auto. 
   Intros h hs y0.
   forward.
   forward.
   forward.
   Exists x. simpl. unfold listrep; fold listrep. entailer!. Exists y. entailer!.
   destruct hs.
   + simpl. unfold listrep; entailer!.
   + inversion H1. 
Qed.

Lemma body_add_void': semax_body Vprog Gprog f_add_void add_void_spec'.
Proof.
start_function.
forward_if. (* if head *)
- forward.
- forward. forward. forward. entailer!!. destruct (eq_dec q nullval); try contradiction; auto.
Qed.

Lemma body_free: semax_body Vprog Gprog f_free free_spec.
Proof.
start_function.
forward. forward. forward. entailer!.
Qed.





























(******** ikke nået hertil endnu *******************)
(******** ikke nået hertil endnu *******************)
(******** ikke nået hertil endnu *******************)

Lemma body_remove: semax_body Vprog Gprog f_remove remove_spec.
Proof.
start_function.
forward.
forward_if (x <> nullval); try contradiction.
- unfold listrep_cons; fold listrep_cons. Intros y. forward.
   entailer!.



unfold listrep; fold listrep. entailer.
   unfold listrep; fold listrep. EExists. entailer!.

entailer!. Exists y. 

y. forward. unfold listrep; fold listrep.


   entailer. unfold listrep; fold listrep. Exists y. entailer!.
   rewrite (listrep_nonnull _ _ x) by auto.
Intros h hs y. forward. entailer.

(* if head *) inversion H0. subst. forward. entailer!.  

2: {} 
forward_if (x = nullval); try contradiction. (* if head *)
- forward. (* head == nullval, which is not possible by assumption.. *)
- rewrite (listrep_nonnull _ _ x) by auto. 
   Intros h hs y0.
   forward.
   forward.
   forward.
   Exists x. simpl. unfold listrep; fold listrep. entailer!. Exists y. entailer!.
   destruct hs.
   + simpl. unfold listrep; entailer!.
   + inversion H1. 
Qed.

(** compiles until this..*)
   
