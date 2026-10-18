/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Sym

/-!
# Capacities of undirected cuts on unordered pairs

This file defines the capacity of a cut for a function on unordered vertex pairs and its simple
support graph. Diagonal pairs never contribute to a cut and are ignored by the support graph.

## Main definitions

* `TauCeti.pairCutCapacity`: the capacity of a cut for weights on unordered vertex pairs.
* `TauCeti.capacitySupport`: the simple support graph of a pair-capacity function.
-/

public section

open Finset

namespace Sym2

variable {V : Type*}

/-- An unordered pair crosses `S` when its two endpoints lie on opposite sides of `S`. -/
def Crosses (p : Sym2 V) (S : Set V) : Prop :=
  (∃ x ∈ p, x ∈ S) ∧ ∃ y ∈ p, y ∉ S

/-- A displayed unordered pair crosses a set exactly when its endpoints lie on opposite sides. -/
@[simp]
theorem crosses_mk_iff {S : Set V} {x y : V} :
    s(x, y).Crosses S ↔ (x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S) := by
  simp only [Crosses, Sym2.mem_iff]
  aesop

/-- Crossing a set is unchanged by exchanging the set with its complement. -/
@[simp]
theorem crosses_compl (p : Sym2 V) (S : Set V) : p.Crosses Sᶜ ↔ p.Crosses S := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp only [crosses_mk_iff, Set.mem_compl_iff, not_not]
      tauto

/-- A diagonal unordered pair crosses no set. -/
theorem not_crosses_diag (x : V) (S : Set V) : ¬s(x, x).Crosses S := by
  simp

/-- A crossing unordered pair is not diagonal. -/
theorem Crosses.not_isDiag {p : Sym2 V} {S : Set V} (h : p.Crosses S) : ¬p.IsDiag := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp only [crosses_mk_iff, mk_isDiag_iff] at h ⊢
      rintro rfl
      simp at h

end Sym2

namespace TauCeti

variable {V K : Type*}

open Classical in
/-- The capacity of the undirected cut with source side `S` for weights on unordered vertex
pairs. Each crossing pair is counted once; diagonal pairs never cross. -/
noncomputable def pairCutCapacity [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) : K :=
  ∑ p : Sym2 V, if p.Crosses (S : Set V) then c p else 0

open Classical in
/-- The defining finite-sum formula for `pairCutCapacity`. -/
theorem pairCutCapacity_def [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) :
    pairCutCapacity c S =
      ∑ p : Sym2 V, if p.Crosses (S : Set V) then c p else 0 :=
  (rfl)

/-- Pair cut capacity is unchanged when the two sides of the cut are exchanged. -/
@[simp]
theorem pairCutCapacity_compl [Fintype V] [DecidableEq V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) :
    pairCutCapacity c Sᶜ = pairCutCapacity c S := by
  classical
  simp only [pairCutCapacity, Finset.coe_compl, Sym2.crosses_compl]

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
