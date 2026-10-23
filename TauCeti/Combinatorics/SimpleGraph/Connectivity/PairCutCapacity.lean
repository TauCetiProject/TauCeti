/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Sym
public import TauCeti.Data.Sym.Crosses
public import TauCeti.Order.Lattice.Submodular

/-!
# Capacities of undirected cuts on unordered pairs

This file defines the capacity of a cut for a function on unordered vertex pairs and its simple
support graph. Diagonal pairs never contribute to a cut and are ignored by the support graph.

## Main definitions

* `TauCeti.pairCutCapacity`: the capacity of a cut for weights on unordered vertex pairs.
* `TauCeti.capacitySupport`: the simple support graph of a pair-capacity function.

## Main result

* `TauCeti.isSubmodular_pairCutCapacity`: a pair-capacity function nonnegative off the diagonal
  has a submodular cut function.
* `TauCeti.isSymmSubmodular_pairCutCapacity`: the same cut function is symmetric submodular.
-/

public section

open Finset

namespace TauCeti

variable {V K : Type*}

open Classical in
/-- The capacity of the undirected cut with source side `S` for weights on unordered vertex
pairs. Each crossing pair is counted once; diagonal pairs never cross. -/
noncomputable def pairCutCapacity [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) : K :=
  ∑ p : Sym2 V, if p.Crosses (S : Set V) then c p else 0

/-- The defining finite-sum formula for `pairCutCapacity`. -/
theorem pairCutCapacity_def [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V)
    [DecidablePred fun p : Sym2 V ↦ p.Crosses (S : Set V)] :
    pairCutCapacity c S =
      ∑ p : Sym2 V, if p.Crosses (S : Set V) then c p else 0 := by
  classical
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Crosses (S : Set V) <;> simp [hp]

/-- Pair cut capacity is unchanged when the two sides of the cut are exchanged. -/
@[simp]
theorem pairCutCapacity_compl [Fintype V] [DecidableEq V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) :
    pairCutCapacity c Sᶜ = pairCutCapacity c S := by
  classical
  simp only [pairCutCapacity, Finset.coe_compl, Sym2.crosses_compl]

/-- The cut function of weights nonnegative on pairs of distinct vertices is submodular.
Diagonal weights are unrestricted. Together with `pairCutCapacity_compl`, this makes it a symmetric
submodular set function. -/
theorem isSubmodular_pairCutCapacity [Fintype V] [DecidableEq V] [AddCommMonoid K]
    [Preorder K] [IsOrderedAddMonoid K] (c : Sym2 V → K)
    (hc : ∀ x y, x ≠ y → 0 ≤ c s(x, y)) :
    IsSubmodular (pairCutCapacity c) := by
  classical
  rw [isSubmodular_def]
  intro S T
  simp only [sup_eq_union, inf_eq_inter]
  simp_rw [pairCutCapacity_def]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro p _
  induction p using Sym2.inductionOn with
  | _ x y =>
    by_cases hxy : x = y
    · subst y
      simp only [Sym2.not_crosses_diag, ↓reduceIte, add_zero, le_refl]
    have hp := hc x y hxy
    have hpp := add_nonneg hp hp
    by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;>
      by_cases hyS : y ∈ S <;> by_cases hyT : y ∈ T <;>
      simp_all

/-- The cut function of weights nonnegative on pairs of distinct vertices is symmetric submodular.
Diagonal weights are unrestricted. -/
theorem isSymmSubmodular_pairCutCapacity [Fintype V] [DecidableEq V] [AddCommMonoid K]
    [Preorder K] [IsOrderedAddMonoid K] (c : Sym2 V → K)
    (hc : ∀ x y, x ≠ y → 0 ≤ c s(x, y)) :
    IsSymmSubmodular (pairCutCapacity c) :=
  ⟨pairCutCapacity_compl c, isSubmodular_pairCutCapacity c hc⟩

/-- Diagonal values do not affect pair cut capacities. -/
theorem pairCutCapacity_eq_of_offDiagonal_eq [Fintype V] [AddCommMonoid K]
    (c d : Sym2 V → K) (h : ∀ x y, x ≠ y → c s(x, y) = d s(x, y)) :
    pairCutCapacity c = pairCutCapacity d := by
  funext S
  classical
  simp only [pairCutCapacity]
  apply sum_congr rfl
  intro p _
  induction p using Sym2.inductionOn with
  | _ x y =>
      split_ifs with hxy
      · exact h x y fun hEq ↦ by subst y; simp at hxy
      · rfl

/-- The simple support graph of a pair-capacity function. Diagonal capacities are ignored. -/
def capacitySupport [Zero K] [LT K] (c : Sym2 V → K) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {p | 0 < c p}

@[simp]
theorem capacitySupport_adj [Zero K] [LT K] (c : Sym2 V → K) (x y : V) :
    (capacitySupport c).Adj x y ↔ x ≠ y ∧ 0 < c s(x, y) := by
  rw [capacitySupport, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq, and_comm]

/-- Changing only diagonal capacities does not change the support graph. -/
theorem capacitySupport_eq_of_offDiagonal_eq [Zero K] [LT K]
    (c d : Sym2 V → K) (h : ∀ x y, x ≠ y → c s(x, y) = d s(x, y)) :
    capacitySupport c = capacitySupport d := by
  ext x y
  simp only [capacitySupport_adj]
  by_cases hxy : x = y
  · simp [hxy]
  · rw [h x y hxy]

end TauCeti
