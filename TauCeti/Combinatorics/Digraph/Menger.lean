/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Digraph.ArrowWalk
public import TauCeti.Combinatorics.Network.Menger.Vertex

/-!
# Menger's theorem for digraphs

A digraph is an arrow family with at most one arrow between each ordered pair of vertices. This
file specializes local vertex Menger to the adjacency arrow family `Digraph.AdjHom D`, translating
the nonadjacency hypothesis `IsEmpty (D.AdjHom s t)` into `¬D.Adj s t`. Paths are
`TauCeti.ArrowWalk`s in that family, so their vertex sequences are exactly chains for `D.Adj` by
`Digraph.arrowWalkEquiv`.

The other directed forms of Menger's theorem need no translation and apply to `D.AdjHom`
directly: the correction for possibly adjacent terminals
(`TauCeti.exists_paths_isMixedSeparator_card_eq`), the set-to-set forms
(`TauCeti.exists_paths_setSeparator_card_eq`) and the arc forms
(`TauCeti.exists_paths_arrowSeparator_card_eq`, `TauCeti.exists_paths_setArrowSeparator_card_eq`),
together with their capacitated and threshold variants. Instantiate them with `Q := D.AdjHom`.
Their finiteness hypotheses on arrows are found by instance search: `Decidable (D.Adj s t)` gives
`Fintype (D.AdjHom s t)`, and every `D.AdjHom v w` is a subsingleton, so it is `Finite`.

## Main results

* `Digraph.exists_paths_vertexSeparator_card_eq`: local vertex Menger for nonadjacent terminals.
* `Digraph.exists_paths_vertexSeparator_sum_eq`: its vertex-capacitated version.
* `Digraph.forall_reachableAvoiding_iff_exists_paths`: its threshold form.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

open Finset TauCeti

universe u

namespace Digraph

variable {V : Type u} {D : Digraph V} {s t : V}

/-! ### Vertex-disjoint paths between two vertices -/

/-- **Vertex-capacitated Menger's theorem for a digraph.** Let `s` and `t` be distinct vertices
with no arrow from `s` to `t`, and let `c v` be the capacity of vertex `v`. Some family of `k`
directed `s`-to-`t` paths respects every nonterminal vertex capacity, and some terminal-excluding
vertex separator has total capacity `k`. -/
theorem exists_paths_vertexSeparator_sum_eq [Finite V] [DecidableEq V] (c : V → ℕ) (hst : s ≠ t)
    (hadj : ¬D.Adj s t) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk D.AdjHom s t) (X : Finset V),
      (∀ i, (P i).IsPath) ∧
      (∀ v, v ≠ s → v ≠ t → #{i | v ∈ (P i).vertices} ≤ c v) ∧
      s ∉ X ∧ t ∉ X ∧ ¬ReachableAvoiding D.AdjHom (X : Set V) s t ∧
      ∑ v ∈ X, c v = k :=
  TauCeti.exists_paths_vertexSeparator_sum_eq c hst (isEmpty_adjHom_iff.2 hadj)

/-- **Menger's theorem for internally vertex-disjoint paths in a digraph.** Between distinct
nonadjacent vertices of a finite digraph, some family of pairwise internally vertex-disjoint
directed paths has the same cardinality as a terminal-excluding vertex separator. -/
theorem exists_paths_vertexSeparator_card_eq [Finite V] (hst : s ≠ t) (hadj : ¬D.Adj s t) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk D.AdjHom s t) (X : Finset V),
      Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      s ∉ X ∧ t ∉ X ∧ ¬ReachableAvoiding D.AdjHom (X : Set V) s t ∧ #X = k :=
  TauCeti.exists_paths_vertexSeparator_card_eq hst (isEmpty_adjHom_iff.2 hadj)

/-- **Menger's theorem for vertex deletion in a digraph, predicate form.** Distinct nonadjacent
vertices remain joined after deleting any fewer than `k` other vertices exactly when there are
`k` pairwise internally vertex-disjoint directed paths between them. -/
theorem forall_reachableAvoiding_iff_exists_paths [Finite V] (hst : s ≠ t) (hadj : ¬D.Adj s t)
    (k : ℕ) :
    (∀ X : Finset V, s ∉ X → t ∉ X → #X < k →
      ReachableAvoiding D.AdjHom (X : Set V) s t) ↔
      ∃ P : Fin k → ArrowWalk D.AdjHom s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) :=
  TauCeti.forall_reachableAvoiding_iff_exists_paths hst (isEmpty_adjHom_iff.2 hadj) k

end Digraph
