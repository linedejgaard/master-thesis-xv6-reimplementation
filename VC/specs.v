From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export proofmode notation.
From iris.prelude Require Import options.

(** General (CAP-style) spec for a concurrent bag ("per-element spec") *)
Record concurrent_bag {Σ} `{!heapGS Σ} := ConcurrentBag {
  is_bag   (s : val) : iProp Σ;
  bag_pers   (s : val) : Persistent (is_bag s);
  new_bag : val;
  bag_push : val;
  bag_pop : val;
  mk_bag_spec   :
    {{{ True }}}
      new_bag #()
    {{{ s, RET s; is_bag s }}};
  bag_push_spec   s v :
    {{{ is_bag s }}} bag_push s v {{{ RET #(); True }}};
  bag_pop_spec   s :
    {{{ is_bag s }}} bag_pop s {{{ ov, RET ov; ⌜ov = NONEV⌝ ∨ ∃ v, ⌜ov = SOMEV v⌝ }}}
}.
Global Arguments concurrent_bag _ {_}.

(** General (HoCAP-style) spec for a concurrent kmem *)


Record concurrent_kmem {Σ} `{!heapGS Σ} := Concurrentkmem {
  is_kmem (N : namespace)    (s : val) : iProp Σ;
  kmem_pers (N : namespace)    (s : val) : Persistent (is_kmem N s);
  new_kmem : val;
  kmem_free : val;
  kmem_alloc : val;
  new_kmem_spec (N : namespace)    :
    {{{ True }}} new_kmem #() {{{ v, RET v; is_kmem N v }}};
  kmem_free_spec (N : namespace)    (Ψ : val → iProp Σ) s (v : loc) :
    {{{ is_kmem N s ∗ Ψ #()}}}
      kmem_free s #v
    {{{ RET #(); Ψ #() }}};
  kmem_alloc_spec (N : namespace)  Ψ s :
    {{{ is_kmem N s ∗
        (Ψ (SOMEV #v)) ∧
        (∗ Ψ NONEV) }}}
      kmem_alloc s
    {{{ v, RET v; Ψ v }}};
}. 
Global Arguments concurrent_kmem _ {_}.
