/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Digraph.ArrowWalk
public import TauCeti.Combinatorics.Network.Menger.Adjacent
public import TauCeti.Combinatorics.Network.Menger.Edge
public import TauCeti.Combinatorics.Network.Menger.SetToSet

/-!
# Menger's theorem for digraphs

A digraph is an arrow family with at most one arrow between each ordered pair of vertices. This
file specializes the directed forms of Menger's theorem to the adjacency arrow family
`Digraph.AdjHom D`. Paths are `TauCeti.ArrowWalk`s in that family, so their vertex sequences are
exactly chains for `D.Adj` by `Digraph.arrowWalkEquiv`. In the local vertex form, the generic
nonadjacency hypothesis `IsEmpty (D.AdjHom s t)` becomes `¬D.Adj s t`.

The local edge, adjacent-terminal, and set-to-set forms retain arrow identities from `D.AdjHom`.
Thus their separators delete directed edges rather than unordered pairs, and the adjacent-terminal
correction counts exactly the arrow from `s` to `t` when it exists. Every `D.AdjHom v w` is a
subsingleton and therefore `Finite`; a decidable adjacency proposition supplies the `Fintype`
instance needed to count the direct arrow in the adjacent-terminal statements.

## Main results

* `Digraph.exists_paths_vertexSeparator_card_eq`: local vertex Menger for nonadjacent terminals.
* `Digraph.exists_paths_vertexSeparator_sum_eq`: its vertex-capacitated version.
* `Digraph.forall_reachableAvoiding_iff_exists_paths`: its threshold form, which holds for
  arbitrary `s` and `t`.
* `Digraph.exists_paths_arrowSeparator_card_eq`: local edge Menger.
* `Digraph.exists_paths_isMixedSeparator_card_eq`: the adjacent-terminal form.
* `Digraph.exists_paths_setSeparator_sum_eq`: vertex-capacitated set-to-set Menger.
* `Digraph.exists_paths_setSeparator_card_eq`: vertex-disjoint set-to-set Menger.
* `Digraph.exists_paths_setArrowSeparator_card_eq`: arrow-disjoint set-to-set Menger.

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

/-- **Menger's theorem for vertex deletion in a digraph, predicate form.** Vertices remain joined
after deleting any fewer than `k` other vertices exactly when there are `k` pairwise internally
vertex-disjoint directed paths between them. -/
theorem forall_reachableAvoiding_iff_exists_paths [Finite V] (k : ℕ) :
    (∀ X : Finset V, s ∉ X → t ∉ X → #X < k →
      ReachableAvoiding D.AdjHom (X : Set V) s t) ↔
      ∃ P : Fin k → ArrowWalk D.AdjHom s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) :=
  TauCeti.forall_reachableAvoiding_iff_exists_paths k

/-! ### Arrow-disjoint paths between two vertices -/

/-- **Menger's theorem for edge-disjoint paths in a digraph.** Between distinct vertices of a
finite digraph, some family of pairwise arrow-disjoint directed paths has the same cardinality as
an arrow set whose deletion destroys reachability. -/
theorem exists_paths_arrowSeparator_card_eq [Finite V] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk D.AdjHom s t)
      (F : Finset (Σ v w, D.AdjHom v w)),
      (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) ∧
      ¬ReachableWithout (F : Set (Σ v w, D.AdjHom v w)) s t ∧ #F = k :=
  TauCeti.exists_paths_arrowSeparator_card_eq hst

/-- **Menger's theorem for edge deletion in a digraph, predicate form.** Vertices remain joined
after deleting any fewer than `k` arrows exactly when there are `k` pairwise arrow-disjoint
directed paths between them. -/
theorem forall_reachableWithout_iff_exists_paths [Finite V] (k : ℕ) :
    (∀ F : Finset (Σ v w, D.AdjHom v w), #F < k →
      ReachableWithout (F : Set (Σ v w, D.AdjHom v w)) s t) ↔
      ∃ P : Fin k → ArrowWalk D.AdjHom s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows :=
  TauCeti.forall_reachableWithout_iff_exists_paths k

/-! ### Paths between adjacent vertices -/

/-- **Menger's theorem for internally vertex-disjoint paths between possibly adjacent vertices of
a digraph.** For distinct `s` and `t`, the direct arrow from `s` to `t`, when present, is counted
separately. After deleting it, a terminal-excluding vertex separator and the remaining internally
disjoint paths have the same cardinality. -/
theorem exists_paths_isMixedSeparator_card_eq [Finite V] [Decidable (D.Adj s t)] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k ⊕ D.AdjHom s t → ArrowWalk D.AdjHom s t) (X : Finset V),
      Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      (∀ e, P (.inr e) = (ArrowWalk.nil s).cons e) ∧
      IsMixedSeparator X (arrowFinset D.AdjHom s t) s t ∧ #X = k :=
  TauCeti.exists_paths_isMixedSeparator_card_eq hst

/-- **Menger's theorem for possibly adjacent vertices of a digraph, predicate form.** After
deleting the direct arrow from `s` to `t` and any fewer than `k` other vertices, `t` remains
reachable from `s` exactly when there are the corresponding internally disjoint paths. -/
theorem forall_not_isMixedSeparator_iff_exists_paths [Finite V] [Decidable (D.Adj s t)]
    (hst : s ≠ t) (k : ℕ) :
    (∀ X : Finset V, #X < k →
      ¬IsMixedSeparator X (arrowFinset D.AdjHom s t) s t) ↔
      ∃ P : Fin k ⊕ D.AdjHom s t → ArrowWalk D.AdjHom s t,
        Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
          Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) :=
  TauCeti.forall_not_isMixedSeparator_iff_exists_paths hst k

/-! ### Vertex-disjoint paths between vertex sets -/

/-- **Vertex-capacitated Menger's theorem between vertex sets of a digraph.** Some packing of
directed paths from `A` to `B` respects every vertex capacity, and some vertex set meeting every
such path has total capacity equal to the size of the packing. The terminal sets may overlap. -/
theorem exists_paths_setSeparator_sum_eq [Finite V] [DecidableEq V] (c : V → ℕ)
    (A B : Finset V) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i))
      (X : Finset V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (∀ v, #{i | v ∈ (P i).vertices} ≤ c v) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding D.AdjHom (X : Set V) a b) ∧
      ∑ v ∈ X, c v = k :=
  TauCeti.exists_paths_setSeparator_sum_eq c A B

/-- **Menger's theorem for vertex-disjoint paths between vertex sets of a digraph.** Some family
of pairwise vertex-disjoint `A`–`B` paths and some vertex set meeting every `A`–`B` path have the
same cardinality. The terminal sets may overlap. -/
theorem exists_paths_setSeparator_card_eq [Finite V] (A B : Finset V) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i))
      (X : Finset V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding D.AdjHom (X : Set V) a b) ∧ #X = k :=
  TauCeti.exists_paths_setSeparator_card_eq A B

/-- **Menger's theorem for vertex deletion between vertex sets of a digraph, predicate form.**
After deleting any fewer than `k` vertices, some vertex of `B` remains reachable from some vertex
of `A` exactly when there are `k` pairwise vertex-disjoint `A`–`B` paths. -/
theorem forall_exists_reachableAvoiding_iff_exists_paths [Finite V] (A B : Finset V) (k : ℕ) :
    (∀ X : Finset V, #X < k → ∃ a ∈ A, ∃ b ∈ B,
      ReachableAvoiding D.AdjHom (X : Set V) a b) ↔
      ∃ (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i)),
        (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices :=
  TauCeti.forall_exists_reachableAvoiding_iff_exists_paths A B k

/-! ### Arrow-disjoint paths between vertex sets -/

/-- **Menger's theorem for arrow-disjoint paths between vertex sets of a digraph.** For disjoint
terminal sets, some family of pairwise arrow-disjoint `A`–`B` paths and some arrow set separating
every vertex of `B` from every vertex of `A` have the same cardinality. -/
theorem exists_paths_setArrowSeparator_card_eq [Finite V] {A B : Finset V}
    (hAB : Disjoint A B) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i))
      (F : Finset (Σ v w, D.AdjHom v w)),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) ∧
      (∀ a ∈ A, ∀ b ∈ B,
        ¬ReachableWithout (F : Set (Σ v w, D.AdjHom v w)) a b) ∧ #F = k :=
  TauCeti.exists_paths_setArrowSeparator_card_eq hAB

/-- **Menger's theorem for arrow deletion between vertex sets of a digraph, predicate form.**
After deleting any fewer than `k` arrows, some vertex of `B` remains reachable from some vertex of
`A` exactly when there are `k` pairwise arrow-disjoint `A`–`B` paths. -/
theorem forall_exists_reachableWithout_iff_exists_paths [Finite V] {A B : Finset V} (k : ℕ) :
    (∀ F : Finset (Σ v w, D.AdjHom v w), #F < k → ∃ a ∈ A, ∃ b ∈ B,
      ReachableWithout (F : Set (Σ v w, D.AdjHom v w)) a b) ↔
      ∃ (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i)),
        (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows :=
  TauCeti.forall_exists_reachableWithout_iff_exists_paths k

end Digraph
