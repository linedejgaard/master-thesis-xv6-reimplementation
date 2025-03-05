From iris.heap_lang Require Import proofmode notation.

(** Basic *)
Definition prog : val := λ: <>,
  let: "l" := ref #40 in
  "l" <- (!"l" + #2);;
  !"l".

Section with_Σ.
  Context `{heapGS Σ}.

  Definition prog_spec :=
    {{{ True }}} prog #() {{{ w, RET w; ⌜w = #42⌝ }}}.

  (* P, Q ⊢ P ∧ Q. *)
  
  Lemma prog_spec_holds : prog_spec.
  Proof.
    unfold prog_spec.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_alloc l as "Hl".
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    wp_pures.
    wp_load.
    iModIntro.
    iApply "HΦ".
    done.
  Qed.

  (** Basic *)
  Definition prog2 : val := λ: "l",
    "l" <- (!"l" + #2);;
    !"l".

  Definition prog2_spec l :=
    {{{ l ↦ #40 }}} prog2 #l {{{ w, RET w; ⌜w = #42⌝ }}}.
  
  Lemma prog2_spec_holds l : prog2_spec l.
  Proof.
    unfold prog2_spec.
    iIntros (Φ) "Hl HΦ".
    wp_lam.
    wp_load.
    wp_store.
    wp_load.
    iModIntro.
    iApply "HΦ".
    done.
  Qed.
    
  (** Basic *)
  Definition prog3 : val := λ: <>,
    let: "l" := ref #40 in
    prog2 "l".

  Definition prog3_spec :=
    {{{ True }}} prog3 #() {{{ w, RET w; ⌜w = #42⌝ }}}.

  (* HΦ : ..., Hl : l ↦ #40 ⊢ prog2_spec_holds l. *)

  Lemma sep_example (P Q R : iProp Σ) :
    (P -∗ Q -∗ R) ⊢ P -∗ Q -∗ R.
  Proof.
    iIntros "HPQR". iIntros "HP HQ".
    iApply ("HPQR" with "HP HQ").
  Qed.
    
  Lemma prog3_spec_holds : prog3_spec.
  Proof.
    unfold prog3_spec.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_alloc l as "Hl".
    wp_pures.
    iApply (prog2_spec_holds with "Hl HΦ").
  Qed.                                       
  
End with_Σ.
