/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic

/-!
# Electrical networks given by conductances

An electrical network on a vertex type `V` is a symmetric nonnegative conductance function
`c : V → V → ℝ`. The pairs of distinct vertices with positive conductance are the edges of the
network; a positive value `c x x` is a loop at `x`, and parallel edges are not modelled separately,
their conductances adding up to one value of `c`. This is the setting in which reversible random
walks on finite graphs and electrical networks are two descriptions of the same object: the walk
steps from `x` to `y` with probability `c x y / c x`, where `c x = ∑ y, c x y` is the weight of
`x` (see `TauCeti.Combinatorics.ElectricalNetwork.RandomWalk`).

The edge-indexed `TauCeti.ResistorNetwork` describes a network by a family of resistors with
positive resistances, which may be parallel. Here a network is determined by its conductance
function alone, which is what the random walk and the voltage problem depend on.

## Main definitions

* `TauCeti.ElectricalNetwork`: a symmetric nonnegative conductance function.
* `TauCeti.ElectricalNetwork.weight`: the weight `c x = ∑ y, c x y` of a vertex, counting a loop
  once.
* `TauCeti.ElectricalNetwork.totalWeight`: the total weight `c_G = ∑ x, c x`.
* `TauCeti.ElectricalNetwork.graph`: the simple graph whose edges join distinct vertices of
  positive conductance; the network is connected when this graph is.
* `TauCeti.ElectricalNetwork.edgeCond`: the conductance of an unordered pair of vertices.

## Main results

* `TauCeti.ElectricalNetwork.weight_eq_zero_iff`: a vertex has weight zero exactly when it carries
  no edge and no loop.
* `TauCeti.ElectricalNetwork.weight_pos_of_preconnected`: on a preconnected, in particular on a
  connected, network with at least two vertices every weight is positive.

## References

* D. A. Levin and Y. Peres, *Markov chains and mixing times*, second edition, American
  Mathematical Society, 2017, §9.1.
* R. Lyons and Y. Peres, *Probability on trees and networks*, Cambridge University Press, 2016,
  §2.1.
-/

public section

open Finset

namespace TauCeti

/-- An electrical network on the vertex type `V`: a conductance `cond x y` for every two
vertices, symmetric and nonnegative. Distinct vertices with positive conductance are joined by an
edge, and `0 < cond x x` is a loop at `x`. -/
@[ext]
structure ElectricalNetwork (V : Type*) where
  /-- The conductance between two vertices. -/
  cond : V → V → ℝ
  /-- Conductances are symmetric. -/
  symm : ∀ x y, cond x y = cond y x
  /-- Conductances are nonnegative. -/
  nonneg : ∀ x y, 0 ≤ cond x y

namespace ElectricalNetwork

variable {V : Type*} (N : ElectricalNetwork V)

/-- The graph of a network: two vertices are adjacent when they are distinct and the conductance
between them is positive. Loops are not edges of this graph. -/
def graph : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => 0 < N.cond x y

/-- Two vertices are adjacent in the graph of a network exactly when they are distinct and the
conductance between them is positive. -/
@[simp]
theorem graph_adj {x y : V} : N.graph.Adj x y ↔ x ≠ y ∧ 0 < N.cond x y := by
  rw [graph, SimpleGraph.fromRel_adj, N.symm y x, or_self]

/-- Adjacent vertices have positive conductance. -/
theorem cond_pos_of_adj {x y : V} (h : N.graph.Adj x y) : 0 < N.cond x y :=
  (N.graph_adj.1 h).2

/-- The conductance of an unordered pair of vertices. -/
def edgeCond : Sym2 V → ℝ :=
  Sym2.lift ⟨N.cond, N.symm⟩

/-- The conductance of the unordered pair `s(x, y)` is `cond x y`. -/
@[simp]
theorem edgeCond_mk (x y : V) : N.edgeCond s(x, y) = N.cond x y :=
  Sym2.lift_mk _ x y

/-- The conductance of an unordered pair is nonnegative. -/
theorem edgeCond_nonneg (e : Sym2 V) : 0 ≤ N.edgeCond e := by
  induction e with
  | _ x y => simpa using N.nonneg x y

/-- Every edge of the graph of a network has positive conductance. -/
theorem edgeCond_pos_of_mem_edgeSet {e : Sym2 V} (h : e ∈ N.graph.edgeSet) : 0 < N.edgeCond e := by
  induction e with
  | _ x y => simpa using N.cond_pos_of_adj h

variable [Fintype V]

/-- The weight `c x = ∑ y, c x y` of a vertex, in which a loop at `x` is counted once. -/
def weight (x : V) : ℝ :=
  ∑ y, N.cond x y

/-- The total weight `c_G = ∑ x, c x = ∑ x, ∑ y, c x y` of a network. On a network without loops
it is twice the sum of the conductances of the edges. -/
def totalWeight : ℝ :=
  ∑ x, N.weight x

/-- The weight of a vertex is the sum of the conductances at it. -/
theorem weight_def (x : V) : N.weight x = ∑ y, N.cond x y := (rfl)

/-- The total weight is the sum of the weights. -/
theorem totalWeight_def : N.totalWeight = ∑ x, N.weight x := (rfl)

/-- The total weight is the double sum of the conductances over ordered pairs. -/
theorem totalWeight_eq_sum_sum : N.totalWeight = ∑ x, ∑ y, N.cond x y := (rfl)

/-- Weights are nonnegative. -/
theorem weight_nonneg (x : V) : 0 ≤ N.weight x :=
  Finset.sum_nonneg fun y _ => N.nonneg x y

/-- The total weight is nonnegative. -/
theorem totalWeight_nonneg : 0 ≤ N.totalWeight :=
  Finset.sum_nonneg fun x _ => N.weight_nonneg x

/-- Every conductance at `x` is at most the weight of `x`. -/
theorem cond_le_weight (x y : V) : N.cond x y ≤ N.weight x :=
  Finset.single_le_sum (fun z _ => N.nonneg x z) (Finset.mem_univ y)

/-- Every weight is at most the total weight. -/
theorem weight_le_totalWeight (x : V) : N.weight x ≤ N.totalWeight :=
  Finset.single_le_sum (fun z _ => N.weight_nonneg z) (Finset.mem_univ x)

/-- A vertex has weight zero exactly when every conductance at it vanishes, that is, when it
carries no edge and no loop. -/
theorem weight_eq_zero_iff {x : V} : N.weight x = 0 ↔ ∀ y, N.cond x y = 0 := by
  simp [weight_def, Finset.sum_eq_zero_iff_of_nonneg fun y _ => N.nonneg x y]

/-- A vertex has positive weight exactly when some conductance at it is positive. -/
theorem weight_pos_iff {x : V} : 0 < N.weight x ↔ ∃ y, 0 < N.cond x y := by
  simp [weight_def, Finset.sum_pos_iff_of_nonneg fun y _ => N.nonneg x y]

/-- A vertex with a neighbour in the graph of the network has positive weight. -/
theorem weight_pos_of_adj {x y : V} (h : N.graph.Adj x y) : 0 < N.weight x :=
  N.weight_pos_iff.2 ⟨y, N.cond_pos_of_adj h⟩

/-- On a preconnected network, in particular on a connected one, with at least two vertices
every weight is positive. -/
theorem weight_pos_of_preconnected [Nontrivial V] (hN : N.graph.Preconnected) (x : V) :
    0 < N.weight x :=
  have ⟨_, hxy⟩ := hN.exists_adj_of_nontrivial x
  N.weight_pos_of_adj hxy

/-- The total weight vanishes exactly when every weight does. -/
theorem totalWeight_eq_zero_iff : N.totalWeight = 0 ↔ ∀ x, N.weight x = 0 := by
  simp [totalWeight_def, Finset.sum_eq_zero_iff_of_nonneg fun x _ => N.weight_nonneg x]

/-- The total weight is positive exactly when some weight is. -/
theorem totalWeight_pos_iff : 0 < N.totalWeight ↔ ∃ x, 0 < N.weight x := by
  simp [totalWeight_def, Finset.sum_pos_iff_of_nonneg fun x _ => N.weight_nonneg x]

/-- A network with an edge has positive total weight. -/
theorem totalWeight_pos_of_adj {x y : V} (h : N.graph.Adj x y) : 0 < N.totalWeight :=
  N.totalWeight_pos_iff.2 ⟨x, N.weight_pos_of_adj h⟩

end ElectricalNetwork

end TauCeti
