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
exactly chains for `D.Adj` by `Digraph.arrowWalkEquiv`.

The local vertex theorem translates the nonadjacency hypothesis `IsEmpty (D.AdjHom s t)` into
`¬D.Adj s t`. The adjacent-terminal theorem counts the direct arrow separately. The set-to-set
theorems cover vertex-disjoint and arc-disjoint paths, including vertex capacities, and the local
arc theorem is their singleton-terminal specialization. The finiteness hypotheses on arrows hold
automatically because every `D.AdjHom v w` is a subsingleton. The adjacent-terminal statements
also assume decidability of the direct adjacency so that its arrow finset can be formed.

## Main results

* `Digraph.exists_paths_vertexSeparator_card_eq`: local vertex Menger for nonadjacent terminals.
* `Digraph.exists_paths_vertexSeparator_sum_eq`: its vertex-capacitated version.
* `Digraph.forall_reachableAvoiding_iff_exists_paths`: its threshold form, which holds for
  arbitrary `s` and `t`.
* `Digraph.exists_paths_isMixedSeparator_card_eq`: local vertex Menger for possibly adjacent
  terminals, counting the direct arrow separately.
* `Digraph.exists_paths_setSeparator_card_eq`: vertex-disjoint set-to-set Menger.
* `Digraph.exists_paths_setSeparator_sum_eq`: vertex-capacitated set-to-set Menger.
* `Digraph.exists_paths_arrowSeparator_card_eq`: local arc Menger.
* `Digraph.exists_paths_setArrowSeparator_card_eq`: arc-disjoint set-to-set Menger.

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

/-! ### Possibly adjacent terminals -/

/-- **Menger's theorem for possibly adjacent vertices of a digraph.** Between distinct vertices
of a finite digraph, some family of internally vertex-disjoint directed paths consists of all
direct arrows together with as many remaining paths as there are vertices in a separator after
the direct arrow has been deleted. -/
theorem exists_paths_isMixedSeparator_card_eq [Finite V] [Decidable (D.Adj s t)] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k ⊕ D.AdjHom s t → ArrowWalk D.AdjHom s t) (X : Finset V),
      Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      (∀ e, P (.inr e) = (ArrowWalk.nil s).cons e) ∧
      IsMixedSeparator X (arrowFinset D.AdjHom s t) s t ∧ #X = k :=
  TauCeti.exists_paths_isMixedSeparator_card_eq hst

/-- **Menger's theorem for possibly adjacent vertices of a digraph, predicate form.** After
deleting the direct arrow and any fewer than `k` other vertices, `t` remains reachable from `s`
exactly when there is a family of distinct, internally vertex-disjoint directed `s`–`t` paths
indexed by `Fin k ⊕ D.AdjHom s t`: `k` paths, plus one more if `D.Adj s t` holds. -/
theorem forall_not_isMixedSeparator_iff_exists_paths [Finite V] [Decidable (D.Adj s t)]
    (hst : s ≠ t) (k : ℕ) :
    (∀ X : Finset V, #X < k →
      ¬IsMixedSeparator X (arrowFinset D.AdjHom s t) s t) ↔
      ∃ P : Fin k ⊕ D.AdjHom s t → ArrowWalk D.AdjHom s t, Function.Injective P ∧
        (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) :=
  TauCeti.forall_not_isMixedSeparator_iff_exists_paths hst k

/-! ### Vertex-disjoint paths between vertex sets -/

/-- **Vertex-capacitated Menger's theorem between vertex sets of a digraph.** Some packing of
directed paths from `A` to `B` respects every vertex capacity and has size equal to the capacity
of a set meeting every directed walk from `A` to `B`. -/
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
of pairwise vertex-disjoint directed paths from `A` to `B` has the same cardinality as a set of
vertices meeting every directed walk from `A` to `B`. -/
theorem exists_paths_setSeparator_card_eq [Finite V] (A B : Finset V) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i))
        (X : Finset V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ReachableAvoiding D.AdjHom (X : Set V) a b) ∧
      #X = k :=
  TauCeti.exists_paths_setSeparator_card_eq A B

/-- **Menger's theorem for vertex-disjoint paths between vertex sets of a digraph, predicate
form.** Every deletion of fewer than `k` vertices leaves some directed walk from `A` to `B`
exactly when there are `k` pairwise vertex-disjoint directed paths from `A` to `B`. -/
theorem forall_exists_reachableAvoiding_iff_exists_paths [Finite V]
    (A B : Finset V) (k : ℕ) :
    (∀ X : Finset V, #X < k →
      ∃ a ∈ A, ∃ b ∈ B, ReachableAvoiding D.AdjHom (X : Set V) a b) ↔
      ∃ (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i)),
        (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).vertices,
          v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices :=
  TauCeti.forall_exists_reachableAvoiding_iff_exists_paths A B k

/-! ### Arc-disjoint paths -/

/-- **Menger's theorem for arc-disjoint paths in a digraph.** Between distinct vertices of a
finite digraph, some family of pairwise arc-disjoint directed paths has the same cardinality as
a set of arcs whose deletion leaves the target unreachable from the source. -/
theorem exists_paths_arrowSeparator_card_eq [Finite V] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k → ArrowWalk D.AdjHom s t)
        (F : Finset (Σ x y, D.AdjHom x y)),
      (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) ∧
      ¬ReachableWithout (F : Set (Σ x y, D.AdjHom x y)) s t ∧ #F = k :=
  TauCeti.exists_paths_arrowSeparator_card_eq hst

/-- **Menger's theorem for arc-disjoint paths in a digraph, predicate form.** The target remains
reachable after deleting any fewer than `k` arcs exactly when there are `k` pairwise arc-disjoint
directed paths from the source to the target. -/
theorem forall_reachableWithout_iff_exists_paths [Finite V] (k : ℕ) :
    (∀ F : Finset (Σ x y, D.AdjHom x y), #F < k →
      ReachableWithout (F : Set (Σ x y, D.AdjHom x y)) s t) ↔
      ∃ P : Fin k → ArrowWalk D.AdjHom s t, (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows :=
  TauCeti.forall_reachableWithout_iff_exists_paths k

/-! ### Arc-disjoint paths between vertex sets -/

/-- **Menger's theorem for arc-disjoint paths between vertex sets of a digraph.** For disjoint
vertex sets `A` and `B`, some family of pairwise arc-disjoint directed paths from `A` to `B` has
the same cardinality as a set of arcs whose deletion separates every vertex of `B` from every
vertex of `A`. -/
theorem exists_paths_setArrowSeparator_card_eq [Finite V] {A B : Finset V}
    (hAB : Disjoint A B) :
    ∃ (k : ℕ) (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i))
        (F : Finset (Σ x y, D.AdjHom x y)),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).vertices, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) ∧
      (∀ a ∈ A, ∀ b ∈ B,
        ¬ReachableWithout (F : Set (Σ x y, D.AdjHom x y)) a b) ∧ #F = k :=
  TauCeti.exists_paths_setArrowSeparator_card_eq hAB

/-- **Menger's theorem for arc-disjoint paths between vertex sets of a digraph, predicate form.**
Every deletion of fewer than `k` arcs leaves some directed walk from `A` to `B` exactly when there
are `k` pairwise arc-disjoint directed paths from `A` to `B`. -/
theorem forall_exists_reachableWithout_iff_exists_paths [Finite V]
    {A B : Finset V} (k : ℕ) :
    (∀ F : Finset (Σ x y, D.AdjHom x y), #F < k →
      ∃ a ∈ A, ∃ b ∈ B, ReachableWithout (F : Set (Σ x y, D.AdjHom x y)) a b) ↔
      ∃ (a b : Fin k → V) (P : ∀ i, ArrowWalk D.AdjHom (a i) (b i)),
        (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).vertices,
          v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows :=
  TauCeti.forall_exists_reachableWithout_iff_exists_paths k

end Digraph
