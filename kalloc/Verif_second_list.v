Require VC.Preface.  (* Check for the right version of VST *)

(* ----------------------------------------------------------------- *)
(** *** Standard boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VC.second_list.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Open Scope logic.

(* ----------------------------------------------------------------- *)
(** *** Functional model *)

(** *** List *)

Definition t_list := Tstruct _list noattr.
Definition t_node := Tstruct _node noattr.

Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_node (y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.


(*Lemma listrep_local_prop: forall il p, listrep il p |--
 !! (is_pointer_or_null p  /\ (p=nullval <-> il=nil)).
Proof.
Admitted.
#[export] Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall il p,
   listrep il p |-- valid_pointer p.
Proof.
  intros. destruct il.
  - unfold listrep. entailer!.
  - unfold listrep. destruct p; Intro y; entailer!.
Qed.
#[export] Hint Resolve listrep_valid_pointer : valid_pointer.*)

Definition add_spec :=
 DECLARE _add
  WITH sh : share, x: val, y: val, s1: list val, s2: list val
  PRE [ tptr t_list , tptr t_node]
     PROP(writable_share sh)
     PARAMS (x; y) GLOBALS()
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_list ]
    EX r: val,
     PROP()
     RETURN (r)
     SEP (listrep sh (s1++s2) r).




(* for describing a segment of list (lseg = list segment) *)
Fixpoint lseg (contents: list val) (x z: val) : mpred :=
  match contents with
  | nil => !! (x = z) && emp
  | h::hs => EX y:val, data_at Tsh t_node (y) x * lseg hs y z
end.

Arguments lseg contents x z : simpl never.

(*  ---> Lemmas related to list segments!! <---  *)
Lemma singleton_lseg: forall (a: val) (x y: val),
  data_at Tsh t_node (y) x |-- lseg [a] x y.
Proof.
  intros. unfold lseg. EExists. entailer!.
Qed.

  (** loops **)
  (* --> there may be a loop e.g. a node points to itself, but this doesn't enable that a pointer can point to two different structures <-- *)
Lemma lseg_maybe_loop: forall (a b x y: val),
  data_at Tsh t_node (y) x * data_at Tsh t_node (y) y 
  |-- lseg [a; b] x y.
Proof.
  intros.
  unfold lseg.
  Exists y.
  Exists y.
  entailer!.
Qed.

(*Lemma loopy_lseg_not_bad: forall (a b c x y: val),
  data_at Tsh t_list (y) x * data_at Tsh t_list (y) y * listrep [c] y 
    |-- FF.
Proof.
  intros.
  unfold listrep.
  Intros u.
  subst.
Check (data_at_conflict Tsh t_list (c, nullval)). 
  sep_apply (data_at_conflict Tsh t_list (c, nullval)). 
  + auto.
  + entailer!.
Qed.*)

  (** the lemma states that two list segments can be concatenated if the end of the first segment is the beginning of the second segment. **)
Lemma lseg_lseg: forall (s1 s2: list val) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros s1.
  induction s1.
  - simpl. unfold lseg at 1. entailer!.
  - intros. unfold lseg; fold lseg. Intros y0. simpl. unfold lseg; fold lseg.
    Exists y0. entailer!. apply IHs1.
Qed.

  (** if you have a list segment (lseg) followed by a complete list (listrep), you can concatenate them into a single complete list (listrep). **)
(*Lemma lseg_list: forall (s1 s2: list val) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intros s1.
  induction s1.
  - intros. simpl. unfold lseg. entailer!.
  - intros. unfold lseg; fold lseg. simpl. Intros y0. unfold listrep; fold listrep. Exists y0. entailer!. apply IHs1.
Qed. *)

(*
The lemma states that for any list sigma and any pointer p, if listrep sigma p holds, then:
    p is either a valid pointer or null.
    p is null if and only if sigma is an empty list (nil).
*)
Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
   Proof.
   intros.
   revert p; induction sigma; intros p.
   - unfold listrep.
     entailer!.
     split; auto.
   - unfold listrep; fold listrep.
     entailer.
    entailer!.
    split; intro.
    + clear - H H2.
      subst p.
      eapply field_compatible_nullval; eauto.
    + inversion H2.
   Qed.

#[export] Hint Resolve listrep_local_facts : saturate_local.

(*
  p should be a valid pointer that points to a list.
*)
Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
   intros.
   unfold listrep.
   destruct sigma; simpl.
  - hint.
    entailer!.
  - Intros y.
    auto with valid_pointer.
Qed.

#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

(** (End of the material repeated from Verif_reverse.v) *)

(* if the pointer is null, then there is no contents and no list *)
Lemma listrep_null: forall contents x,
  x = nullval ->
  listrep contents x = !! (contents=nil) && emp.
Proof.
  intros. apply pred_ext.
  - subst. entailer!. 
    + destruct H. apply H; auto.
    + assert (contents = []) . { destruct H; apply H; auto. }
      subst. unfold listrep. entailer!.
  - subst. unfold listrep. entailer!.
Qed.  

(* if the pointer is not null, then there is at least one element *)
Lemma listrep_nonnull: forall contents x,
  x <> nullval ->
  listrep contents x =
    EX h: val, EX hs: list val, EX y:val,
      !! (contents = h :: hs) && data_at Tsh t_list (h, y) x * listrep hs y.
Proof.
  intros; apply pred_ext.
  - destruct contents.
    + unfold listrep. entailer!. 
    + unfold listrep; fold listrep. Intros y. Exists v contents y. entailer!. 
  - Intros h hs y. rewrite H0. unfold listrep at 2; fold listrep. Exists y. entailer!.
Qed.


(** sums **)

(* Example definition of val_add if not already defined: *)
Definition val_add (v1 v2: val) : val :=
  match v1, v2 with
  | Vint i1, Vint i2 => Vint (Int.add i1 i2)
  | _, _ => Vundef  (* handle other cases appropriately *)
  end.

(* Example definition of val_of_Z if not already defined: *)
Definition val_of_Z (z: Z) : val := Vint (Int.repr z).

(* Now define sum_val *)
Definition sum_val (l: list val) : val := fold_right val_add (val_of_Z 0) l.


(** *** API spec *)

Definition sumlist_spec :=
 DECLARE _sumlist
  WITH sigma : list val, p: val
  PRE [ tptr t_list ]
     PROP()
     PARAMS (p)
     SEP (listrep sigma p)
  POST [ tuint ]
     PROP()
     RETURN (sum_val sigma)
     SEP (listrep sigma p).

Definition main_spec :=
DECLARE _main
    WITH gv : globals
    PRE [] main_pre prog tt gv
    POST [ tint ] main_post prog gv.
      

Definition Gprog := [sumlist_spec; main_spec]. (* Packaging the Gprog and Vprog *)

Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
start_function.
repeat forward.
forward_while
( EX s1a: list val, EX h: val,  EX i: Z, EX s1c: list val, EX t: val, EX u: val,
        PROP (sigma = s1a ++ h :: s1c \/ sigma = [])
        LOCAL (temp _t p;
        temp _s (sum_val (sublist 0 i sigma)); temp _p p)
        SEP (lseg s1a p t;
             data_at Tsh t_list (h, u) t;
             listrep s1c u))%assert.

- entailer!. repeat EExists. entailer!.
  destruct p; try inversion PNp; induction sigma.
  + split. right; auto. rewrite sublist_of_nil. auto.
  + split. left. let a0 := [].
  

  + entailer!. 
    EExists. EExists.
    * unfold sum_val. try rep_lia. 

destruct sigma.
  + repeat EExists. entailer!. 


( EX s1a: list val, EX h: val, EX s1c: list val, EX t: val, EX u: val,
  PROP (
    s1 = s1a ++ h :: s1c;
    0 <= i <= (Z.of_nat (length sigma)
  )
LOCAL (
  temp _t p;
  temp _s (sum_val (sublist 0 i sigma)); temp _p p
  )
LOCAL (temp _h h; temp _t t; temp _t u)
SEP (lseg s1a x t;
     data_at Tsh t_list (h, u) t;
     listrep s1c u;
     listrep s2 y))%assert.

forward_while(
  EX i,
    PROP (0 <= i <= (Z.of_nat (length sigma))
    )
    LOCAL (
      temp _t p;
      temp _s (sum_val (sublist 0 i sigma)); temp _p p
      )
    SEP (
      listrep sigma p
      )
).
- Exists 0; entailer!.
- entailer!.
- forward. destruct p; try inversion HRE. unfold listrep.
  forward.
  + forward. unfold isptr in HRE.

forward_while(
  EX i,
    PROP (0 <= i <= (Z.of_nat (length sigma)))
    LOCAL (
      temp _t p; 
      temp _s ( (sum_val (sublist 0 i sigma)))
      )
    SEP (listrep sigma p)
).
- Exists 0. entailer!.
- entailer!.
- destruct sigma as [ | h hs]. 
  + unfold listrep.
+ admit.
Admitted.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
Admitted.


#[export] Existing Instance NullExtension.Espec. (* boilerplate, when you don't have input/output *)

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sumlist.
semax_func_cons body_main.
Qed.




(*************************************************************************************************)
(** Now, let's prove this [append] function correct. *)


(** *** API spec *)

Definition sumlist_spec :=
 DECLARE _sumlist
  WITH sigma : list val, p: val
  PRE [ tptr t_list ]
     PROP()
     PARAMS (p)
     SEP (listrep sigma p)
  POST [ tuint ]
     PROP()
     LOCAL(temp ret_temp  ( ( (sum_val sigma))))
     SEP (listrep sigma p).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
     PROP() RETURN (Vint (Int.repr (3+2+1))) SEP(TT).

Definition Gprog : funspecs :=   ltac:(with_library prog [
sumlist_spec; main_spec]).

Lemma body_sum_list: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
  start_function.
  repeat forward.
  forward_while (EX acc: Z, EX s: list val, EX q: val,
    PROP (sum_val s = val_of_Z acc)
    LOCAL (temp _t p; temp _s (Vint (Int.repr acc)); temp _p q)
    SEP (listrep s q)).
    - entailer!. Exists 0 sigma p.
      entailer!. induction sigma.
      + unfold sum_val, val_of_Z; simpl; auto.
      + admit.
    - entailer!. 
      destruct s as [| h t].
      + unfold listrep. entailer!. admit.
      + admit.
    - admit.
    - forward. entailer!. admit. admit.
Admitted.


Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
    start_function. 
    forward_call.
    forward_call (v_value, 10).
    forward.
    entailer!.
Qed.

#[export] Existing Instance NullExtension.Espec. (* boilerplate, when you don't have input/output *)

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_increment.
semax_func_cons body_main.
Qed.