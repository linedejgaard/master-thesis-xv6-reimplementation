From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export proofmode notation.
From iris.prelude Require Import options.

(** General (CAP-style) spec for a concurrent bag ("per-element spec") *)
Record concurrent_bag {Σ} `{!heapGS Σ} := ConcurrentBag {
  is_bag (P : val → iProp Σ) (s : val) : iProp Σ;
  bag_pers (P : val → iProp Σ) (s : val) : Persistent (is_bag P s);
  new_bag : val;
  bag_push : val;
  bag_pop : val;
  mk_bag_spec (P : val → iProp Σ) :
    {{{ True }}}
      new_bag #()
    {{{ s, RET s; is_bag P s }}};
  bag_push_spec (P : val → iProp Σ) s v :
    {{{ is_bag P s ∗ P v }}} bag_push s v {{{ RET #(); True }}};
  bag_pop_spec (P : val → iProp Σ) s :
    {{{ is_bag P s }}} bag_pop s {{{ ov, RET ov; ⌜ov = NONEV⌝ ∨ ∃ v, ⌜ov = SOMEV v⌝ ∗ P v }}}
}.
Global Arguments concurrent_bag _ {_}.

(** General (HoCAP-style) spec for a concurrent kmem *)


Record concurrent_kmem {Σ} `{!heapGS Σ} := Concurrentkmem {
  is_kmem (N : namespace) (P : list loc → iProp Σ) (s : val) : iProp Σ;
  kmem_pers (N : namespace) (P : list loc → iProp Σ) (s : val) : Persistent (is_kmem N P s);
  new_kmem : val;
  kmem_free : val;
  kmem_alloc : val;
  new_kmem_spec (N : namespace) (P : list loc → iProp Σ) :
    {{{ P [] }}} new_kmem #() {{{ v, RET v; is_kmem N P v }}};
  kmem_free_spec (N : namespace) (P : list loc → iProp Σ) (Ψ : val → iProp Σ) s (v : loc) :
    {{{ is_kmem N P s ∗ ∀ xs, P xs ={⊤ ∖ ↑ N}=∗ P (v :: xs) ∗ Ψ #()}}}
      kmem_free s #v
    {{{ RET #(); Ψ #() }}};
  kmem_alloc_spec (N : namespace) (P : list loc → iProp Σ) Ψ s :
    {{{ is_kmem N P s ∗
        (∀ v xs, P (v :: xs) ={⊤ ∖ ↑ N}=∗ P xs ∗ Ψ (SOMEV #v)) ∧
        (P [] ={⊤ ∖ ↑ N}=∗ P [] ∗ Ψ NONEV) }}}
      kmem_alloc s
    {{{ v, RET v; Ψ v }}};
}.
Global Arguments concurrent_kmem _ {_}.
