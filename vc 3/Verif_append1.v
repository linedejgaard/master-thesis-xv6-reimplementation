(** * Verif_append1: List segments *)

(** Here is a little C program, [append.c]

    #include <stddef.h>

    struct list {int head; struct list *tail;};

    struct list *append (struct list *x, struct list *y) {
      struct list *t, *u;
      if (x==NULL)
        return y;
      else {
        t = x;
        u = t->tail;
        while (u!=NULL) {
          t = u;
          u = t->tail;
        }
        t->tail = y;
        return x;
      }
    }

In this chapter, we will learn to verify this in-place linked-list-append
operation. That is, two original lists will be destructed and a new list,
the concatenation of them, will be constructed in this program.
As we did in previous chapters, we import VST and the C program's AST. *)

Require VC.Preface. (* Check for the right version of VST *)

Require Import VST.floyd.proofauto.
Require Import VC.append.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Specification of the [append] function. *)

(** Here we just copy what we have defined in [Verif_reverse] *)

Definition t_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list val) (p: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_list (h,y) p  *  listrep hs y
 | nil => 
    !! (p = nullval) && emp
 end.

Arguments listrep sigma p : simpl never.

(** Then we can easily describe the functionality of this [append]. *)

Definition append_spec :=
 DECLARE _append
  WITH x: val, y: val, s1: list val, s2: list val
  PRE [ tptr t_list , tptr t_list]
     PROP()
     PARAMS (x; y)
     SEP (listrep s1 x; listrep s2 y)
  POST [ tptr t_list ]
    EX r: val,
     PROP()
     RETURN(r)
     SEP (listrep (s1++s2) r).

Definition Gprog : funspecs := [ append_spec ].

(* ================================================================= *)
(** ** List segments. *)

(** When verifying this program, a critical step is to figure out
a correct loop invariant. If we try to simulate this program,
especially the loop in it, we may want a loop invariant which
can be illustrated by the following diagram.
(The following diagram is best demonstrated with a monospaced font. )

        +---+---+            +---+---+   +---+---+   +---+---+   
  x ==> |   |  ===> ... ===> |   | t ==> | b | u ==> |   |  ===> ... 
        +---+---+            +---+---+   +---+---+   +---+---+

      | <========= s1a =========> |       (b)       | <==== s1c ====> |
      | <============================= s1 ==========================> |

        +---+---+   +---+---+   +---+---+   
  y ==> |   |  ===> |   |   ==> |   |  ===> ... 
        +---+---+   +---+---+   +---+---+

      | <================ s2 =================> |
*)

(** To describe this loop invariant, we need a separation logic predicate to
describe the partial linked list from address [x] to address [t] with contents
[s1a]. This must a new predicate different from [listrep] because [listrep]
describes linked lists ending with [NULL] which is not the case here. We call
this new predicate [lseg], pronounced "list-segment". *)

Fixpoint lseg (contents: list val) (x z: val) : mpred :=
  match contents with
  | nil => !! (x = z) && emp
  | h::hs => EX y:val, data_at Tsh t_list (h, y) x * lseg hs y z
  end.

Arguments lseg contents x z : simpl never.

(** Now, we can prove some useful properties about [lseg]. *)

(** **** Exercise: 1 star, standard (singleton_lseg) *)
Lemma singleton_lseg: forall (a: val) (x y: val),
  data_at Tsh t_list (a, y) x |-- lseg [a] x y.
Proof.
  intros. unfold lseg. EExists. entailer!.
Qed.
(** [] *)

(** It is critical to observe that a partial linked list defined by
 [lseg s x y] may have a loop. For example, the following diagram does
 satisfy [lseg [a; b] x y].
(The following diagram is best demonstrated with a monospaced font. )

        +---+---+   +---+---+   
  x ==> | a | y ==> | b | y ====+ 
        +---+---+   +- -+---+   |
                      ^         |
                      |         |
                      +=========+

We can prove this formally. *)

Lemma lseg_maybe_loop: forall (a b x y: val),
  data_at Tsh t_list (a, y) x * data_at Tsh t_list (b, y) y 
  |-- lseg [a; b] x y.
Proof.
  intros.
  unfold lseg.
  Exists y.
  Exists y.
  entailer!.
Qed.

(** Is our definition of [lseg] wrong? The answer is no because a loopy [lseg]
cannot connect to a nonempty linked list. For instance, we can prove that

  data_at Tsh t_list (a, y) x * data_at Tsh t_list (b, y) y * listrep [c] y

will lead to a contradication. Here, the first two separating conjuncts build
a loopy [lseg] and the third separating conjunct is a nonempty [listrep]. *)

Lemma loopy_lseg_not_bad: forall (a b c x y: val),
  data_at Tsh t_list (a, y) x * data_at Tsh t_list (b, y) y * listrep [c] y 
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
Qed.

(** Important note!  The proof above demonstrates the use of the [sep_apply]
 tactic.  Step through that part of the proof to see what [sep_apply] does. *)

(** Now we can prove the following theorems about partial linked
 lists and complete linked lists. *)

(** **** Exercise: 1 star, standard (lseg_lseg) *)
Lemma lseg_lseg: forall (s1 s2: list val) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros s1.
  induction s1.
  - simpl. unfold lseg at 1. entailer!.
  - intros. unfold lseg; fold lseg. Intros y0. simpl. unfold lseg; fold lseg.
    Exists y0. entailer!. apply IHs1.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (lseg_list) *)
Lemma lseg_list: forall (s1 s2: list val) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intros s1.
  induction s1.
  - intros. simpl. unfold lseg. entailer!.
  - intros. unfold lseg; fold lseg. simpl. Intros y0. unfold listrep; fold listrep. Exists y0. entailer!. apply IHs1.
Qed. 
(** [] *)

(** Is it possible to define [lseg] in a different way so that loopy 
   situations can be banned?  Yes.  We discuss this near the end of 
   the chapter. *)

(* ================================================================= *)
(** ** Proof of the [append] function *)

(** Before verifying the functional correctness of [append], we still need
to add lemmas to hint databases for separation logic predicates. Readers
may copy proofs from [Verif_reverse] or just skip down to "End of the
material". *)

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
   Proof.
   intros.
   (** We will prove this entailment by induction on sigma *)
   revert p; induction sigma; intros p.
   - (** In the base case, [sigma] is nil.  We can unfold the definition
      of [listrep] to see what that means. *)
    unfold listrep.
    (** Now we have an entailment with a proposition [p=nullval] on the left.
    To move that proposition above the line, we could do [Intros], but
    it's easier just to call on [entailer!] to see how it can simplify (and perhaps
    partially solve) this entailment goal: *)
     entailer!.
    (* The [entailer!] has left an ordinary proposition, which is easy to solve. *)
     split; auto.
   - (** In the inductive case, we can again unfold the definition
      of [listrep (a::sigma)]; but then it's good to fold [listrep sigma].
      Replace the semicolon [;] with a period in the next line, to see why. *)
    unfold listrep; fold listrep.
   
    (** Warning!  Sometimes [entailer!] is too aggressive.  If we use it
     here, it will throw away the left-hand side because it doesn't
     understand how to look inside an EXistential quantitier.  The
     exclamation point [!] is a warning that [entailer!] can turn a
     provable goal into an unprovable goal.  Uncomment the next line
     and see what happens.  Then put the comment marks back. *)
    (* entailer!. *)
   
    (** The preferred way to handle [EX y:t] on the left-hand-side of an
    entailment is to use [Intros y.]  Uncomment this to try it out, then
    put the comment marks back. *)
    (* Intros y. *)
   
    (** A less agressive entailment-reducer is [entailer] without the
       exclamation point. This one never turns a provable goal into an
       unprovable goal.  Here it will Intro the EX-bound variable y. *)
    entailer.
   
    (** Should you use [entailer!] or [entailer] in ordinary proofs?
     Usually [entailer!] is best: it's faster, and it does more work for you.
     Only if you  find that [entailer!] has gone into a dead end, should
     you use [entailer] instead. *)
   
    (** Here it is safe to use [entailer!] *)
    entailer!.
    (** Notice that entailer! has put several facts above the line:
     [field_compatible t_list [] p] and [value_fits t_list (a,y)] come from the
     [saturate_local] hint database, from the [data_at] conjunct;  and
     [is_pointer_or_null y] and [y=nullval <-> sigma=[]] come from the
     the [listrep] conjunct, using the induction hypothesis [IHsigma].
   
     Now, let's split the goal and take the two cases separately. *)
    split; intro.
    +
     clear - H H2.
     subst p.
     (** It happens that [field_compatible _ _ p] implies [isptr p], *)
   Check field_compatible_isptr.
      (* : forall (t : type) (path : list gfield) (p : val),
          field_compatible t path p -> isptr p *)
      (**  The predicate isptr excludes the null pointer, *)
   Print isptr.
     (* = fun v : val => match v with Vptr _ _ => True | _ => False end *)
   Print nullval.
     (* = if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero *)
     (** Therefore [H] is a contradiction.  We can proceed with, *)
   Check field_compatible_nullval.
     (* = forall (CS : compspecs) (t : type) (f : list gfield) (P : Type),
          field_compatible t f nullval -> P *)
     eapply field_compatible_nullval; eauto.
    + (*The case  [a::sigma=[] -> p=nullval] is easy, by inversion: *)
      inversion H2.
   Qed.
#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
   intros.
   (** The main point is to unfold listrep. *)
   unfold listrep.
   (** Now we can prove it by case analysis on sigma; we don't even need
     induction. *)
   destruct sigma; simpl.
  - (** The  nil case is easy: *)
    hint.
    entailer!.
  - (**  The cons case *)
    Intros y.
    (** Now this solves using the Hint database [valid_pointer], because the
       [data_at Tsh t_list (v,y) p] on the left is enough to prove the goal. *)
    auto with valid_pointer.
Qed.

#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

(** (End of the material repeated from Verif_reverse.v) *)

(** In C programs, we test whether the head pointer of a linked list is null
 to determine whether that list is empty or not. Thus, from a separating
 conjunct [listrep contents x], it is useful to prove [contents = nil] (or
 [contents <> nil]) when knowing that [x = nullval] (or [x <> nullval]). The
 following two lemmas state such correlation. They will be used several
 times in the C function [append]'s correctness proof. *)

(** **** Exercise: 1 star, standard (listrep_null) *)
Lemma listrep_null: forall contents x,
  x = nullval ->
  listrep contents x = !! (contents=nil) && emp.
Proof.
(** Hint: One way to prove [P=Q], where P and Q are [mpred]s,
  is to apply [pred_ext] and then prove [P|--Q] and [Q|--P]. *)
  intros. apply pred_ext.
  - subst. entailer!. 
    + destruct H. apply H; auto.
    + assert (contents = []) . { destruct H; apply H; auto. }
      subst. unfold listrep. entailer!.
  - subst. unfold listrep. entailer!.
Qed.  
(** [] *)

(** **** Exercise: 1 star, standard (listrep_nonnull) *)
Lemma listrep_nonnull: forall contents x,
  x <> nullval ->
  listrep contents x =
    EX h: val, EX hs: list val, EX y:val,
      !! (contents = h :: hs) && data_at Tsh t_list (h, y) x * listrep hs y.
Proof.
(** Again, [pred_ext] will be useful here. *)
  intros; apply pred_ext.
  - destruct contents.
    + unfold listrep. entailer!. 
    + unfold listrep; fold listrep. Intros y. Exists v contents y. entailer!. 
  - Intros h hs y. rewrite H0. unfold listrep at 2; fold listrep. Exists y. entailer!.
Qed.
(** [] *)

(** Now, let's prove this [append] function correct. *)

(** **** Exercise: 3 stars, standard (body_append) *)
Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if. (* if (x == NULL) *)
- (* If-then *)
  (** This if-then branch handles the cases in which [x] is null. In other
   words, [s1] should be [nil]. We can easily derive this by [listrep_null].
   The rest of the proof in this branch is left as an exercise. *)
  rewrite (listrep_null _ x) by auto.
  (* FILL IN HERE *) 
  forward.
  EExists. entailer!. rewrite app_nil_l. entailer.
- (* If-else *)
  (** This time, we know that [x] is not null; thus [s1] should
    be nonempty. *)
  rewrite (listrep_nonnull _ x) by auto.
  Intros h r u.
  forward. (* t = x; *)
  forward. (* u = t -> tail; *)

  (** After symbolically executing two assignment commands, we arrive
     at the while loop. As mentioned above, we can verify it using
     the following loop invariant. *)
  forward_while
      ( EX s1a: list val, EX b: val, EX s1c: list val, EX t: val, EX u: val,
        PROP (s1 = s1a ++ b :: s1c)
        LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
        SEP (lseg s1a x t;
             data_at Tsh t_list (b, u) t;
             listrep s1c u;
             listrep s2 y))%assert.
 + (* current assertion implies loop invariant *)
      Exists (@nil val) h r x u.
      subst s1. entailer!. unfold lseg; entailer!.
 + (* loop test is safe to execute *)
      entailer!.
 +  (* loop body preserves invariant *)
    (** We know [u] is not null from the fact that the loop condition
       is true. Thus we can represent [s1c] in the form of [(c :: s1d)]. *)
    clear h r u H0; rename u0 into u.
    rewrite (listrep_nonnull _ u) by auto.
    Intros c s1d z.
    forward. (* t = u; *)
    forward. (* u = t -> tail; *)

    (** In the end of the loop body, we need to re-establish the
      loop invariant. At this point, the memory layout can be
      illustrated by the following diagram.

      (The following diagram is best demonstrated with a monospaced font. )

                                 new t       new u
                                   |           |
                                   |           |
                 +---+---+   +---+---+   +---+---+   +---+---+   
  x ==> ... ===> |   | t ==> | b | u ==> | c | z ==> |   |  ===> ... 
                 +---+---+   +---+---+   +---+---+   +---+---+

      | <===== s1a =====> |   (b)         (c)      | <==== s1d ====> |
      | <========== new s1a ========> |  (new b)   | <== new s1c ==> |

        +---+---+   +---+---+   +---+---+   
  y ==> |   |  ===> |   |   ==> |   |  ===> ... 
        +---+---+   +---+---+   +---+---+
      | <================ s2 =================> |

 Clearly, [s1a ++ b :: nil] should be the new value of [s1a];  [c] should be
 the new value of [b]; [s1d] should be the new value of [s1c]; [u] should be
 the new value of [t]; and [z] should be the new value of [u]. The next 
 command instantiates the existentially quantified variables in our loop
 invariant accordingly. *)

   Exists ((s1a ++ b :: nil),c,s1d,u,z). unfold fst, snd.

  (** As usual, we try [entailer!] to solve this proof goal. This time,
 [entailer!] does not solve it directly. Instead, two simplified proof goals
 are left. Their proofs are left for the reader, using [app_assoc], 
 [singleton_lseg] and [lseg_lseg]. *)
    entailer!.
    * (* FILL IN HERE *) 
      rewrite <- app_assoc. simpl. auto.
    * (* FILL IN HERE *) 
      sep_apply singleton_lseg.
      rewrite sepcon_comm.
      apply lseg_lseg.
 + (* after the loop *)
   (** After exiting the loop, the loop condition must be false, i.e.
    [u] is the null pointer. Thus [s1c = nil] and [s1 = s1a ++ [b]]. *)    
  clear h r u H0; rename u0 into u.
  rewrite (listrep_null s1c) by auto.
  Intros.
  subst s1c.

  (** The rest of the proof is standard. Hint, [singleton_lseg],
    [lseg_lseg] and/or [lseg_list] may be useful. *)
    (* FILL IN HERE *) 
    forward.
    forward. Exists x. sep_apply singleton_lseg. entailer!. 
    rewrite <- app_assoc.
    sep_apply sepcon_comm. sep_apply lseg_lseg. sep_apply lseg_list. rewrite app_assoc. entailer!. 
  Qed.
(** [] *)

(* ================================================================= *)
(** ** Additional exercises: more proofs about list segments *)

(** For verifying the C function [append], it is enough to have only three
 separation logic proof rules about [lseg]: [singleton_lseg], [lseg_lseg]
 and [lseg_list]. The following exercises are other important properties
 of [lseg]. *)

(** **** Exercise: 1 star, standard: (lseg2listrep) *)
Lemma lseg2listrep: forall s x,
  lseg s x nullval |-- listrep s x.
Proof.
(* FILL IN HERE *)
  intros s. induction s.
  - intros. unfold lseg. unfold listrep. entailer!.
  - unfold listrep; fold listrep. unfold lseg; fold lseg. intros. Intros y.
    Exists y. entailer!.
Qed. 
(** [] *)

(** **** Exercise: 1 star, standard: (listrep2lseg) *)
Lemma listrep2lseg: forall s x,
  listrep s x |-- lseg s x nullval.
Proof.
(* FILL IN HERE *)
  intros s. induction s. 
  - intros. unfold listrep; unfold lseg; entailer!.
  - intros. unfold listrep; fold listrep. unfold lseg; fold lseg. Intros y.
  Exists y. entailer!.
Qed.  
(** [] *)

Corollary lseg_listrep_equiv: forall s x,
  lseg s x nullval = listrep s x.
Proof.
  intros.
  apply pred_ext.
  + apply lseg2listrep.
  + apply listrep2lseg.
Qed.

(** **** Exercise: 2 stars, standard: (lseg_lseg_inv) *)
Lemma lseg_lseg_inv: forall s1 s2 x z,
  lseg (s1 ++ s2) x z |-- EX y: val, lseg s1 x y * lseg s2 y z.
Proof.
  intros s1.
  induction s1.
  - intros. simpl. EExists. unfold lseg at 2. entailer!.
  - simpl. unfold lseg at 1; fold lseg. intros. Intros mid. unfold lseg at 2; fold lseg.
    sep_apply IHs1. Intros y. Exists y.
    Exists mid. entailer!.
Qed. 
(** [] *)

(** **** Exercise: 2 stars, standard: (loopy_lseg_no_connection) *)
Lemma loopy_lseg_no_connection: forall s1 s2 x y z,
  s1 <> nil ->
  s2 <> nil ->
  x = y ->
  lseg s1 x y * lseg s2 y z |-- FF.
Proof.
  intros s1.
  induction s1; try contradiction.
  destruct s2; try contradiction.
  intros.
  Check (data_at_conflict).
  unfold lseg; fold lseg.
  Intros y0. Intros y1. rewrite <- sepcon_assoc. subst.
  sep_apply (data_at_conflict Tsh t_list (v, y1)); auto.
  entailer!.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Additional exercises: loop-free list segments *)

(** In the following exercise, try to redo the proof above
  using a different partial-linked-list predicate.

 We have mentioned that the [lseg] predicate allows a loopy structure,
 which is quite counterintuitive. Here is an alternate definition that
 prohibits loops: *)

Fixpoint nt_lseg (contents: list val) (x z: val) : mpred :=
  match contents with
  | nil => !! (x = z) && emp
  | h::hs => EX y:val, !! (x <> z) 
                   && data_at Tsh t_list (h, y) x * nt_lseg hs y z
  end.

Arguments nt_lseg contents x z : simpl never.

(** Here, "nt" means no-touch. *)

(** The difference between [nt_lseg] and [lseg] is the extra proposition
  [x <> z] in the nonempty situation. This extra clause in [nt_lseg] 
  prevents loop structures.

  The proof theories of [nt_lseg] and [lseg] are a bit different as
  well. The following diagram shows that the counterpart of [lseg_lseg]
  is not valid! 

        +---+---+   +---+---+   +---+---+   +---+---+   
  x ==> | a | u ==> | b | y ==> | c | v ==> | d | u ===+
        +---+---+   +- -+---+   +---+---+   +---+---+  |
                      ^                                |
                      |                                |
                      +================================+

  In this example, both [ [a; b] ] and [ [c; d] ] are stored in loop-free 
  partial linked lists but it is not true for their concatenation. In 
  general, if [(nt_lseg s1 x y)] and [(nt_lseg s2 y z)] describe two 
  loop-free partial linked lists, the assertion

    (nt_lseg s1 x y * nt_lseg s2 y z)

  cannot ensure that the structure is loop free. Specifically, the address
  [z] may be used in [(nt_lseg s1 x y)]. In other words,

   nt_lseg s1 x y * nt_lseg s2 y z |-/- nt_lseg (s1 ++ s2) x z 
*)

(** For [nt_lseg], the following proof rules are useful. *)

(** **** Exercise: 2 stars, standard, optional (nt_lseg) *) 
Lemma singleton_nt_lseg: forall (contents: list val) (a x y: val),
  data_at Tsh t_list (a, y) x * listrep contents y |--
  nt_lseg [a] x y * listrep contents y.
Proof.
(* FILL IN HERE *) 
  intro.
  induction contents.
  - intros. unfold listrep; entailer!. unfold nt_lseg. Exists nullval. entailer!.
  - intros. unfold listrep; fold listrep. Intros y0. Exists y0. 
    sep_apply sepcon_comm.  
    sep_apply IHcontents. entailer!.
    unfold nt_lseg. Intros y1. Exists y. entailer!.
Qed. 
(** [] *)

(** **** Exercise: 2 stars, standard, optional (singleton_nt_lseg') *) 
Lemma singleton_nt_lseg': forall (a b x y z: val),
  data_at Tsh t_list (a, y) x * data_at Tsh t_list (b, z) y |--
  nt_lseg [a] x y * data_at Tsh t_list (b, z) y.
Proof.
intros. unfold nt_lseg. entailer!. Exists y. entailer!.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (nt_lseg_nt_lseg) *) 
Lemma nt_lseg_nt_lseg: forall (s1 s2: list val) (a x y z u: val),
  nt_lseg s1 x y * nt_lseg s2 y z * data_at Tsh t_list (a, u) z |--
  nt_lseg (s1 ++ s2) x z * data_at Tsh t_list (a, u) z.
Proof.
(** Hint:  This lemma illustrates the most classic case where aggressive
 [cancel] can turn a provable goal into an unprovable goal.  For that reason,
  you may need to use [entailer] rather than [entailer!] at one point. *)
(* FILL IN HERE *) 
intro s1. induction s1.
- intros. unfold nt_lseg. entailer.
- intros. simpl. entailer. unfold nt_lseg; fold nt_lseg. Intros y0. entailer. Exists y0.
  entailer. sep_apply IHs1. entailer!.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (nt_lseg_list) *) 
Lemma nt_lseg_list: forall (s1 s2: list val) (x y: val),
  nt_lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intro.
  induction s1.
  - intros. simpl. unfold nt_lseg. entailer!.
  - intros. unfold nt_lseg; fold nt_lseg. Intros y0. simpl. unfold listrep at 2; fold listrep. EExists. entailer!.
    Search listrep. apply IHs1.
Qed.
(** [] *)

(** Now, we will use [nt_lseg] instead of [lseg] in the loop invariant to
prove [body_append]. *)

(** **** Exercise: 3 stars, standard, optional (body_append_alter1) *) 
Lemma body_append_alter1: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if. (* if (x == NULL) *)
- (* If-then *)
 rewrite (listrep_null _ x) by auto.
 (* FILL IN HERE *) 
  forward. simpl. Exists y. entailer!.
- (* If-else *)
 rewrite (listrep_nonnull _ x) by auto.
 Intros h r u.
 forward. (* t = x; *)
 forward. (* u = t -> tail; *)
 (** Now use [forward_while] to verify this while loop.  Remember,
  [forward_while] will generate four proof goals: current precondition 
  implies loop invariant; loop test is safe to execute; loop body preserves
  invariant; and the correctness of after-loop commands. *)
  forward_while
  ( EX s1a: list val, EX b: val, EX s1c: list val, EX t: val, EX u: val,
    PROP (s1 = s1a ++ b :: s1c)
    LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
    SEP (lseg s1a x t;
         data_at Tsh t_list (b, u) t;
         listrep s1c u;
         listrep s2 y))%assert.
  + intros. Exists (@nil val) h r x u. entailer!. unfold lseg; entailer!.
  + entailer.
  + clear h r u H0. rewrite (listrep_nonnull _ u0) by auto.
    Intros h0 hs y0.
    forward. forward.
    entailer!.
    (* EX a : ((((list val * val) * list val) * val) * val) *)
    
    Exists ((((s1a ++ b :: nil), h0), hs), u0, y0). simpl. entailer!. 
    * rewrite <- app_assoc. simpl. auto. 
    * sep_apply singleton_lseg. rewrite <- sepcon_comm. sep_apply lseg_lseg.
      entailer.
  + forward. forward_return. 
    assert (s1c = []). {apply H4. auto. }
    Exists x. rewrite H1.
    entailer!.
    unfold listrep; fold listrep. entailer!.
    sep_apply singleton_lseg. sep_apply sepcon_comm.
    sep_apply lseg_lseg.
    sep_apply lseg_list. entailer!.
Qed.
(** [] *)

(* 2023-03-25 11:30 *)
