/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Walk.Chord

/-!
# Chordal graphs

A simple graph is *chordal* when every cycle of length at least four has a chord. Here this is
expressed through induced containment (`SimpleGraph.IsIndContained`, written `⊴`): `G` is chordal
when `cycleGraph n ⊴ G` for no `n ≥ 4`. A cycle without a chord spans an induced cycle graph, and an
induced cycle graph is a cycle without a chord, so this is the usual definition;
`SimpleGraph.IsChordal.length_eq_three_of_isChordless` states the first half of this in terms of
walks.

Chordality passes to graphs induced-contained in a chordal graph, in particular to induced
subgraphs and to isomorphic graphs. Complete graphs are chordal, and the cycle graphs on at least
four vertices are not.

## Main definitions

* `SimpleGraph.IsChordal G`: no cycle graph on at least four vertices is an induced subgraph of `G`.

## Main results

* `SimpleGraph.IsChordal.of_isIndContained`, `SimpleGraph.IsChordal.induce`: chordality passes to
  induced subgraphs.
* `SimpleGraph.IsChordal.length_eq_three_of_isChordless`: in a chordal graph, every chordless cycle
  has length three.
* `SimpleGraph.isChordal_top`, `SimpleGraph.not_isChordal_cycleGraph`: complete graphs are chordal,
  and cycle graphs on at least four vertices are not.

## References

* R. Diestel, *Graph Theory*, Graduate Texts in Mathematics 173, Springer, Section 5.5.
* L. Vandenberghe and M. S. Andersen, *Chordal Graphs and Semidefinite Optimization*, Foundations
  and Trends in Optimization 1 (4), 2014, Section 3.1.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A simple graph is *chordal* when no cycle graph on at least four vertices is an induced
subgraph of it: every cycle of length at least four has a chord. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ n, 4 ≤ n → ¬cycleGraph n ⊴ G

theorem isChordal_def : G.IsChordal ↔ ∀ n, 4 ≤ n → ¬cycleGraph n ⊴ G :=
  Iff.rfl

/-- A chordal graph contains no induced cycle graph on at least four vertices. -/
theorem IsChordal.not_isIndContained (hG : G.IsChordal) {n : ℕ} (hn : 4 ≤ n) :
    ¬cycleGraph n ⊴ G :=
  hG n hn

/-- A graph contained as an induced subgraph in a chordal graph is chordal. -/
theorem IsChordal.of_isIndContained (hG : G.IsChordal) (h : H ⊴ G) : H.IsChordal :=
  fun n hn hH ↦ hG n hn (hH.trans h)

/-- Every induced subgraph of a chordal graph is chordal. -/
theorem IsChordal.induce (hG : G.IsChordal) (s : Set V) : (G.induce s).IsChordal :=
  hG.of_isIndContained (Embedding.induce s).isIndContained

/-- Chordality is invariant under graph isomorphism. -/
theorem Iso.isChordal_iff (e : G ≃g H) : G.IsChordal ↔ H.IsChordal :=
  ⟨fun h ↦ h.of_isIndContained e.isIndContained', fun h ↦ h.of_isIndContained e.isIndContained⟩

/-- In a chordal graph, every chordless cycle has length three. -/
theorem IsChordal.length_eq_three_of_isChordless (hG : G.IsChordal) {u : V} {p : G.Walk u u}
    (hp : p.IsCycle) (hc : p.IsChordless) : p.length = 3 := by
  have := hp.three_le_length
  by_contra hne
  exact hG.not_isIndContained (by lia) (hc.cycleGraph_isIndContained hp)

/-- Complete graphs are chordal. -/
theorem isChordal_top : (⊤ : SimpleGraph V).IsChordal := fun n hn h ↦ by
  have := cycleGraph_eq_top_iff.1 (eq_top_of_isIndContained_top h)
  lia

/-- A cycle graph on at least four vertices is not chordal. -/
theorem not_isChordal_cycleGraph {n : ℕ} (hn : 4 ≤ n) : ¬(cycleGraph n).IsChordal :=
  fun h ↦ h.not_isIndContained hn .rfl

end SimpleGraph
