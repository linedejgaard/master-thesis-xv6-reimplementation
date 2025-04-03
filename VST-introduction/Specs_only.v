(** * Spec_stdlib: Specification of external kalloc, kfree, exit functions *)

(* ################################################################# *)
(** * Abstract Predicate Definition *)

Require VC.Preface. (* Check for the right version of VST *)
Require Import VST.floyd.proofauto.
Require Import VC.client1.

Require VST.floyd.library.  (* Only needed for the next line *)

(*  

  compspecs (short for composite specifications) is a parameter that describes how struct and union types are represented in memory for a given C program.

  PROBLEMS WITH PRE-DEFINDED kalloc_token (we don't want it to be dependent on compspecs):
        That is, [kalloc_token] takes an implicit compspecs argument,
      and the interpretation of the [type] argument depends on the
      compspecs.  Basically, the [kalloc_token] needs to know how many
      bytes the kalloc'd record is, so it needs the compspecs in order
      to interpret the type.
          But now we are doing _modular_ C programming, in which each .c file
      can have its own struct and union types -- that is, its own compspecs.
      Our [kalloc_token] with a compspecs parameter cannot assume that
      every module will have the same compspecs.  For modular programming,
      we'll start with a more primitive form,  [kalloc_token_sz], that just 
      depends on the _size_ of the object, of type [Z].  No compspecs required.
          Later in this file, we show how to recover the type-based
      [kalloc_token] _within_ each module.

  
   In the memory-manager APD we have two abstract predicates, [mem_mgr]
   and [kalloc_token].  The predicate [mem_mgr] represents the state
   of the memory manager's kfree list.  That is, when you call [kfree(p)]
    you might imagine that the memory-block at address p gets
    added back into a kfree list (or some other data structure), and
    when you call [kalloc(n)] then it takes a block from the kfree list.
    Since the internal representation of the kfree list is private to
     this module ([stdlib]), it's an abstract predicate.

*)

Record MallocFreeAPD := {
   mem_mgr: globals -> mpred; (* Predicate that represents the state of the memory manager's kfree list *)
   kalloc_token_sz: share -> Z -> val -> mpred; (* Predicate that represents the memory allocation token *)
   kalloc_token_sz_valid_pointer: forall sh sz p, (* Proof obligation that states:      If the allocated size sz is non-positive (sz <= 0), then kalloc_token_sz should guarantee that p is a valid pointer. *)
      sz <= 0 -> kalloc_token_sz sh sz p |-- valid_pointer p;
   kalloc_token_sz_local_facts:  forall sh sz p, (* This ensures that any pointer p for which kalloc_token_sz holds is kalloc-compatible. *)
      kalloc_token_sz sh sz p |-- !! malloc_compatible sz p
}.

#[export] Hint Resolve kalloc_token_sz_valid_pointer : valid_pointer.
#[export] Hint Resolve kalloc_token_sz_local_facts : saturate_local.

(* ################################################################# *)
(** * Abstract Specification Interface *)

(** As usual, build a Section to parameterize the interface by the APD: *)
Section MallocFreeASI.
Variable M:MallocFreeAPD.

(** Specification of [kalloc] has the same issue with [compspecs] that we
  discussed above for [kalloc_token]:  That is, we need the ASI to be 
  independent of any particular module's struct/union declarations.
  So we will define [kalloc_spec_sz] which is a size-based, not type-based,
  specification. *)

Definition kfree_spec_sz :=
    DECLARE _kfree1
      WITH n:Z, p:val, gv: globals
      PRE [ tptr tvoid ]
          PROP ()
          PARAMS (p) GLOBALS (gv)
          SEP (mem_mgr M gv;
                 if eq_dec p nullval then emp
                 else (kalloc_token_sz M Ews n p * memory_block Ews n p))
                 (*
                    kalloc_token_sz M Ews n p: A token that proves p was allocated with size n.
                    memory_block Ews n p: A memory block of size n exists at p.
                 *)
       POST [ Tvoid ]
          PROP ()
          LOCAL ()
          SEP (mem_mgr M gv).

Definition kalloc_spec_sz :=
 DECLARE _kalloc1
   WITH n:Z, gv: globals
   PRE [ size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       PARAMS (Vptrofs (Ptrofs.repr n)) GLOBALS (gv)
       SEP (mem_mgr M gv)
    POST [ tptr tvoid ] EX p:_, (* The return value p is existentially quantified, meaning we don’t specify it explicitly, but we describe its properties. *)
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr M gv;
             if eq_dec p nullval then emp
            else (kalloc_token_sz M Ews n p * memory_block Ews n p)).


Definition MallocFreeASI:funspecs := [ kalloc_spec_sz; kfree_spec_sz].

End MallocFreeASI.




(* ################################################################# *)
(** * Type-based specification of kalloc and kfree *)

(** Of course, it is much easer for the user to use a funspec for
  kalloc whose postcondition has a [data_at_] of the right type.
  So here we will define an alternate [kalloc_token] and [kalloc_spec]
  that uses compspecs and types. *)

Definition kalloc_token {cs: compspecs} (M:MallocFreeAPD) sh t v := 
   !! field_compatible t [] v && 
   kalloc_token_sz M sh (sizeof t) v.

Lemma kalloc_token_valid_pointer: forall {cs: compspecs} M sh t p, 
      sizeof t <= 0 -> kalloc_token M sh t p |-- valid_pointer p.
Proof. intros. unfold kalloc_token.
 apply andp_left2. apply kalloc_token_sz_valid_pointer; auto.
Qed.

Ltac kalloc_token_data_at_valid_pointer :=
  (* If the size of t is unknown, can still prove valid pointer
      from (kalloc_token sh t p * ... * data_at[_] sh t p)  *)
  match goal with |- ?A |-- valid_pointer ?p =>
   match A with
   | context [kalloc_token _ _ ?t p] =>
         try (assert (sizeof t <= 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         try (assert (sizeof t > 0)
	  by (simpl sizeof in *; rep_lia); fail 1);
         destruct (zlt 0 (sizeof t));
         auto with valid_pointer
   | context [kalloc_token_sz _ _ ?n p] =>
         try (assert (n <= 0) by rep_lia; fail 1);
         try (assert (n > 0) by rep_lia; fail 1);
         destruct (zlt 0 n);
         auto with valid_pointer
   end
 end.

#[export] Hint Extern 1 (kalloc_token _ _ _ _ |-- valid_pointer _) =>
  (simple apply kalloc_token_valid_pointer; data_at_valid_aux) : valid_pointer.
#[export] Hint Extern 4 (_ |-- valid_pointer _) => kalloc_token_data_at_valid_pointer : valid_pointer.

Lemma kalloc_token_local_facts:  forall {cs: compspecs} M sh t p,
      kalloc_token M sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold kalloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply kalloc_token_sz_local_facts.
Qed.
#[export] Hint Resolve kalloc_token_local_facts : saturate_local.

Definition kalloc_spec (M:MallocFreeAPD) {cs: compspecs} (t: type) :=
 DECLARE _kalloc1
   WITH gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true; (* complete_legal_cosu_type is a property related to C types, ensuring that a type is complete, legal, and does not contain an incomplete struct/union type. *)
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr M gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr M gv;
             if eq_dec p nullval then emp
            else (kalloc_token M Ews t p * data_at_ Ews t p)).

Definition kfree_spec (M:MallocFreeAPD)  {cs: compspecs} (t: type) :=
 DECLARE _kfree1
   WITH p: val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr M gv;
              if eq_dec p nullval then emp
              else (kalloc_token M Ews t p * data_at_ Ews t p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr M gv).

(* ================================================================= *)
(** ** How to use the type-based [kalloc_spec] *)

(** Both [kalloc_spec_sz] and [kalloc_spec] are specifications of the 
  same kalloc function, so any given program (.c file) can be verified
  using either of the specs.  However, since the ASI provides
  [kalloc_spec_sz], then in order to use [kalloc_spec] in the verification
  of the client, one must do [forward_call] with the (optional)
  [funspec_sub] argument.

   Here we prove that (for any compspecs), 
    [kalloc_spec_sz] implies [kalloc_spec]. *)

Lemma kalloc_spec_sub:
 forall  (M:MallocFreeAPD) {cs: compspecs} (t: type), 
   funspec_sub (snd (kalloc_spec_sz M)) (snd (kalloc_spec M t)).
Proof.
  do_funspec_sub. rename w into gv. clear H.
  Exists (sizeof t, gv) emp. simpl; entailer!.
  intros tau ? ?. Exists (eval_id ret_temp tau).
  entailer!.
  if_tac; auto.
  unfold kalloc_token.
  assert_PROP (field_compatible t [] (eval_id ret_temp tau)).
  { entailer!.
    apply malloc_compatible_field_compatible; auto. }
  entailer!.
  rewrite memory_block_data_at_; auto.
Qed.

Lemma kfree_spec_sub:
 forall (M:MallocFreeAPD) {cs: compspecs} (t: type), 
   funspec_sub (snd (kfree_spec_sz M)) (snd (kfree_spec M t)).
Proof.
  do_funspec_sub. destruct w as [p gv]. clear H.
  Exists (sizeof t, p, gv) emp. simpl; entailer!.
  if_tac; trivial.
  sep_apply data_at__memory_block_cancel.
  unfold kalloc_token; entailer!.
Qed.

(** Now, the pattern for using [kalloc_spec] will be as shown in
  [VSU_stack], like this:

   [forward_call (kalloc_spec_sub M t) gv]

   [forward_call (kfree_spec_sub M (Tstruct _cons noattr)) (q, gv)]

   It works like this:  [t] (or, for example, [Tstruct _cons noattr]) is
   any type of the client's choosing, interpreted using the client's own
   compspecs.  [forward_call] looks up [kalloc] in the imported
   ASIs (that is, in the Gprog), and finds [kalloc_spec_sz] as its 
   specification.   Then it uses the [funspec_sub] proof to adapt
   the spec into [kalloc_spec M {cs} t], where the [cs] argument is
   instantiated using the _client's_  compspecs, as desired.

   And similarly for [kfree].
*)

(* ================================================================= *)
(** ** Next Chapter: [VSU_stack] *)

(* 2023-03-25 11:30 *)
