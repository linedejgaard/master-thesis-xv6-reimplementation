(** abstract spec interface *)
Require Import VST.floyd.proofauto.
Require Import VC.ASI_kalloc.
Require Import VC.kalloc.
Require Import VC.kallocfun.
Require Import VC.kalloc_kfree_definitions.
Require Import VC.tactics.

Global Open Scope funspec_scope.


(******************************)

(*** kalloc token type... *)
Definition my_kalloc_token {cs: compspecs} K sh t p :=
  !! field_compatible t [] p && (* this should work because of memory_block_data_at_*)
  (kalloc_token' K sh (sizeof t) p).

Lemma my_kalloc_token_valid_pointer:
  forall K (sh : share) (t : type) (p : val),
  my_kalloc_token K sh t p |-- valid_pointer p.
Proof.
  intros. 
  unfold my_kalloc_token. apply andp_left2.
  sep_apply kalloc_token'_local_facts.
  entailer!.
Qed.

Ltac kalloc_token_data_at_valid_pointer :=
  match goal with |- ?A |-- valid_pointer ?p =>
   match A with
   | context [my_kalloc_token _ _ ?t p] =>
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

#[export] Hint Extern 1 (my_kalloc_token _ _ _ _ |-- valid_pointer _) =>
  (simple apply my_kalloc_token_valid_pointer; data_at_valid_aux) : valid_pointer.
#[export] Hint Extern 4 (_ |-- valid_pointer _) => kalloc_token_data_at_valid_pointer : valid_pointer.

Lemma my_kalloc_token_local_facts: forall K {cs: compspecs} sh t p,
      my_kalloc_token K sh t p |-- !! (field_compatible t [] p /\ (
        0 < sizeof t <= PGSIZE
        /\ malloc_compatible (sizeof t) p 
        /\ malloc_compatible (PGSIZE) p
        /\ writable_share sh
        /\ malloc_compatible (sizeof t) p)).
Proof. intros.
 unfold my_kalloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 sep_apply kalloc_token'_local_facts. entailer!.
Qed.
#[export] Hint Resolve my_kalloc_token_local_facts : saturate_local.


Lemma my_kalloc_token_split: 
 forall K (sh: share) (t: type) (p: val),
 my_kalloc_token K (sh) (t) (p)
  = 
  !! field_compatible t [] p &&
  (kalloc_token' K sh (sizeof t) p).
Proof.
  intros. apply pred_ext.
  - unfold my_kalloc_token. entailer.
  - unfold my_kalloc_token. apply andp_right.
    + apply andp_left1. entailer.
    + apply andp_left2. apply derives_refl.
Qed.

Fixpoint my_kalloc_tokens (K:KallocFreeAPD) (sh: share) (n: nat) (p: val) (size: Z) (t:type): mpred :=
  match n with
  | S n' => 
      (sepcon
      (my_kalloc_token K sh t p)
      (my_kalloc_tokens K sh n' (offset_val size p) size t)) (* Move to the next slot *)
  | O => !! (p = nullval) && emp
  end.

Definition my_kalloc_tokens_range K (sh: share) (p_start p_end: val) (size: Z) :=
    match p_start, p_end with
    | Vptr b_s p_s, Vptr b_e p_e =>
      if (sameblock p_start p_end) then
        my_kalloc_tokens K sh (Z.to_nat (compute_c p_start p_end size)) p_start size
      else !! (p_start = nullval) && emp
    | _ , _ => !! (p_start = nullval) && emp
    end.

Arguments my_kalloc_tokens_range K sh p_start p_end size : simpl never.

Lemma my_kalloc_tokens_local_prop: forall K sh n p size t, 
  my_kalloc_tokens K sh n p size t |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros K sh n.
  induction n as [| n' IH].
  - unfold my_kalloc_tokens. entailer!. split; split; intros; auto; auto_contradict; try rep_lia.
  - unfold my_kalloc_tokens; fold my_kalloc_tokens. intros. sep_apply IH. entailer!. destruct p; auto_contradict.
  split; split; intros; try rep_lia; auto; auto_contradict.
Qed.
#[export] Hint Resolve kalloc_tokens_local_prop : saturate_local.

(************************ specs *********************)

Definition kfree_spec (K:KallocFreeAPD) {cs: compspecs} (t: type) := 
  DECLARE _kfree
      WITH new_head:val, gv:globals, sh:share, ls: list val, xx:Z, original_freelist_pointer:val
      PRE [ tptr tvoid]
        PROP(
              is_pointer_or_null new_head
              ) 
        PARAMS (new_head) GLOBALS(gv)
        SEP (
          ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer *
          (if eq_dec new_head nullval then emp
          else (my_kalloc_token K sh (t) new_head))
        )
      POST [ tvoid ]
        PROP()
        RETURN () 
        SEP (
          if eq_dec new_head nullval then 
          ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer
          else 
          ASI_kalloc.mem_mgr K gv sh (original_freelist_pointer::ls) xx new_head
            ).

Definition kalloc_spec (K:KallocFreeAPD) {cs: compspecs} (t: type) :=
DECLARE _kalloc
WITH gv:globals, sh:share, ls: list val, xx:Z, original_freelist_pointer:val
PRE [ ]
    PROP(0 <= (sizeof t) <= PGSIZE;
            complete_legal_cosu_type t = true;
            natural_aligned natural_alignment t = true) 
    PARAMS () GLOBALS(gv)
    SEP ( ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer )  
POST [ tptr tvoid ]
    PROP()
    RETURN (original_freelist_pointer) 
    SEP (
      if (eq_dec original_freelist_pointer nullval) then
        (ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer * emp)
      else 
        (
          EX next ls',
          (!! (next :: ls' = ls) &&
              my_kalloc_token K sh t original_freelist_pointer *
              ASI_kalloc.mem_mgr K gv sh ls' xx next
        )
        )
    ).

Definition kfree_loop_spec (K:KallocFreeAPD) {cs: compspecs} (t: type) := 
  DECLARE _kfree_loop
  WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z
  PRE [ tptr tvoid, tint ]
      PROP(
          isptr pa1 /\
          Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
          0 <= n <= Int.max_signed
      ) 
      PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
      SEP (
          my_kalloc_tokens K sh (Z.to_nat n)%nat pa1 PGSIZE t *
          ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer
      )
  POST [ tvoid ]
      EX head, EX added_elem, (* TODO: fix top and next is the same?? *)
      PROP( 
          added_elem = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE original_freelist_pointer) /\
          head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE original_freelist_pointer)++ls))
          )
          RETURN () (* we return the head like in the pop function*)
          SEP 
          (
            ASI_kalloc.mem_mgr K gv sh (added_elem++ls) xx head
          ).

(************** convert to size version ***************)

Lemma kalloc_spec_sub:
  forall  (K:KallocFreeAPD) {cs: compspecs} (t: type), 
    funspec_sub (snd (kalloc_spec' K _kalloc)) (snd (kalloc_spec K t)).
  Proof.
    do_funspec_sub. 
    entailer.
    destruct w.
    repeat (destruct p).
    Exists (sizeof t, g0, s, l, z, v) emp. entailer.
    if_tac.
    - entailer!. entailer!.
    - entailer!.
      + entailer!. Exists next ls'. entailer!. unfold my_kalloc_token. 
      assert_PROP (field_compatible t [] (eval_id ret_temp x)).
      { entailer!.
        apply malloc_compatible_field_compatible; auto. }
      entailer.
Qed.

Lemma kfree_spec_sub:
forall  (K:KallocFreeAPD) {cs: compspecs} (t: type), 
  funspec_sub (snd (kfree_spec' K _kfree)) (snd (kfree_spec K t)).
Proof.
  do_funspec_sub. 
  destruct w as [[[[[new_head gv] sh] ls] xx] original_freelist_pointer].
  Exists (sizeof t, new_head, gv, sh, ls, xx, original_freelist_pointer) emp.
  entailer!.
  destruct (EqDec_val new_head nullval) eqn:Heq; entailer.
  unfold my_kalloc_token. entailer.
Qed.

Ltac simplify_kalloc_token :=
  repeat (
    rewrite kalloc_token_sz_split;
    unfold my_kalloc_token
  );
  entailer!.

Lemma my_kalloc_tokens_entails_kalloc_tokens_sz:
  forall n K sh pa1 t,
    my_kalloc_tokens K sh (Z.to_nat n) pa1 PGSIZE t
    |-- kalloc_tokens_sz sh (sizeof t) pa1 PGSIZE (Z.to_nat n).
Proof.
  intros n.
  induction (Z.to_nat n).
  - intros. 
  unfold my_kalloc_tokens, kalloc_tokens_sz. entailer.
  - intros. unfold my_kalloc_tokens, kalloc_tokens_sz. 
  fold my_kalloc_tokens; fold kalloc_tokens_sz.
  sep_apply IHn0. entailer!. unfold my_kalloc_token.
  apply andp_left2.
  sep_apply kalloc_token'_local_facts. unfold kalloc_token_sz. entailer!. 
Qed.


Lemma kfree_loop_spec_sub:
forall  (K:KallocFreeAPD) {cs: compspecs} (t: type), 
  funspec_sub (snd (kfree_loop_spec' K)) (snd (kfree_loop_spec K t)).
Proof.
  do_funspec_sub.
  destruct w as [[[[[[sh pa1] original_freelist_pointer] xx] gv] ls] n].
  Exists (sh, pa1, original_freelist_pointer, xx, gv, ls, n, sizeof t, PGSIZE) emp.
  entailer!.
  -intros tau ?.
  Exists (hd nullval
            (pointers_with_original_head (Z.to_nat n + 1) pa1 PGSIZE original_freelist_pointer ++
            ls))
          (pointers_with_original_head (Z.to_nat n) pa1 PGSIZE original_freelist_pointer).
          entailer!.
          assert (kallocfun.PGSIZE = PGSIZE). { unfold kallocfun.PGSIZE, PGSIZE; auto. }
          apply derives_refl.
    - sep_apply my_kalloc_tokens_entails_kalloc_tokens_sz. entailer!. apply derives_refl.
    
    generalize dependent pa1. induction (Z.to_nat n).
      + unfold my_kalloc_tokens, kalloc_tokens_sz. intros. entailer!.
      + intros. unfold my_kalloc_tokens, kalloc_tokens_sz. fold my_kalloc_tokens; fold kalloc_tokens_sz. 
        sep_apply IHn0; auto. 
        sep_apply my_kalloc_tokens_entails_kalloc_tokens_sz.

  rewrite mem_mgr_split.
  unfold my_kalloc_tokens.
  Exists (s, v0, g0, s, l, z, v) emp.
  (*Exists (sizeof t, v0, g0, s, l, z, v) emp.*)
  entailer!.
  destruct (EqDec_val v0 nullval) eqn:Heq; entailer.
  unfold my_kalloc_token. entailer.
Qed.




