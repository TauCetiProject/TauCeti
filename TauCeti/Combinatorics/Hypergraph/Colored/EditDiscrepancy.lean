/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity

/-!
# Edit discrepancy of colored three-uniform hypergraphs

The edit discrepancy `H.editDiscrepancy3 H'` of two colorings of the triples of `V` is six times
the number of unordered triples on which they disagree, divided by `|V|³`. Equivalently, it is
the fraction of all `|V|³` ordered triples of vertices whose entries are distinct and form a
triple on which the colorings disagree.
`H.Approximates3 H' ε` says that the edit discrepancy is at most `ε`.

The discrepancy is a pseudometric: it is nonnegative, symmetric, zero on the diagonal, and
satisfies the triangle inequality, so approximations compose with their errors added. The
vertex count is `Nat.card V`, so no finiteness hypothesis is needed: on an infinite vertex type
the denominator vanishes and every discrepancy is `0`.

## Main definitions

* `TauCeti.Colored3Graph.editDiscrepancy3`: the normalized number of disagreeing triples.
* `TauCeti.Colored3Graph.Approximates3`: approximation within a given edit discrepancy.

## Main results

* `TauCeti.Colored3Graph.editDiscrepancy3_triangle`: the triangle inequality.
* `TauCeti.Colored3Graph.Approximates3.trans`: approximations compose, adding their errors.
-/

public section

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*}

/-- Six times the number of unordered triples on which `H` and `H'` disagree, normalized by
`|V|³`. -/
noncomputable def editDiscrepancy3 (H H' : Colored3Graph κ V) : ℚ :=
  6 * {s | H.color s ≠ H'.color s}.ncard / (Nat.card V : ℚ) ^ 3

/-- The edit discrepancy counts disagreeing triples, normalized by `|V|³`. -/
theorem editDiscrepancy3_def (H H' : Colored3Graph κ V) :
    H.editDiscrepancy3 H' = 6 * {s | H.color s ≠ H'.color s}.ncard / (Nat.card V : ℚ) ^ 3 :=
  (rfl)

/-- The edit discrepancy is nonnegative. -/
theorem editDiscrepancy3_nonneg (H H' : Colored3Graph κ V) : 0 ≤ H.editDiscrepancy3 H' := by
  rw [editDiscrepancy3_def]
  positivity

/-- The edit discrepancy is symmetric. -/
theorem editDiscrepancy3_comm (H H' : Colored3Graph κ V) :
    H.editDiscrepancy3 H' = H'.editDiscrepancy3 H := by
  simp only [editDiscrepancy3_def, ne_comm]

/-- A coloring has edit discrepancy `0` from itself. -/
@[simp]
theorem editDiscrepancy3_self (H : Colored3Graph κ V) : H.editDiscrepancy3 H = 0 := by
  simp [editDiscrepancy3_def]

/-- The **triangle inequality** for the edit discrepancy. -/
theorem editDiscrepancy3_triangle (H₁ H₂ H₃ : Colored3Graph κ V) :
    H₁.editDiscrepancy3 H₃ ≤ H₁.editDiscrepancy3 H₂ + H₂.editDiscrepancy3 H₃ := by
  -- On an infinite vertex type every discrepancy has denominator `0`.
  cases finite_or_infinite V
  · simp only [editDiscrepancy3_def, ← add_div, ← mul_add]
    gcongr
    -- A triple on which `H₁` and `H₃` disagree is one on which `H₂` disagrees with one of them.
    have hsub : {s | H₁.color s ≠ H₃.color s} ⊆
        {s | H₁.color s ≠ H₂.color s} ∪ {s | H₂.color s ≠ H₃.color s} := by
      intro s hs
      by_contra h
      simp_all
    exact_mod_cast (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  · simp [editDiscrepancy3_def]

/-- `H` approximates `H'` within `ε` when their edit discrepancy is at most `ε`. -/
def Approximates3 (H H' : Colored3Graph κ V) (ε : ℝ) : Prop :=
  (H.editDiscrepancy3 H' : ℝ) ≤ ε

/-- Approximation within `ε` means that the edit discrepancy is at most `ε`. -/
theorem approximates3_iff (H H' : Colored3Graph κ V) (ε : ℝ) :
    H.Approximates3 H' ε ↔ (H.editDiscrepancy3 H' : ℝ) ≤ ε :=
  Iff.rfl

/-- A coloring approximates itself within any nonnegative error. -/
theorem approximates3_self (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 ≤ ε) :
    H.Approximates3 H ε := by
  simpa [approximates3_iff] using hε

namespace Approximates3

variable {H₁ H₂ H₃ : Colored3Graph κ V} {ε δ : ℝ}

/-- Approximation is symmetric. -/
theorem symm (h : H₁.Approximates3 H₂ ε) : H₂.Approximates3 H₁ ε := by
  rwa [approximates3_iff, editDiscrepancy3_comm]

/-- Approximation within `ε` implies approximation within any larger error. -/
theorem mono (h : H₁.Approximates3 H₂ ε) (hεδ : ε ≤ δ) : H₁.Approximates3 H₂ δ :=
  h.trans hεδ

/-- Approximations compose, with their errors added. -/
theorem trans (h₁₂ : H₁.Approximates3 H₂ ε) (h₂₃ : H₂.Approximates3 H₃ δ) :
    H₁.Approximates3 H₃ (ε + δ) := by
  rw [approximates3_iff] at *
  calc (H₁.editDiscrepancy3 H₃ : ℝ)
      ≤ (H₁.editDiscrepancy3 H₂ : ℝ) + H₂.editDiscrepancy3 H₃ := by
        exact_mod_cast editDiscrepancy3_triangle H₁ H₂ H₃
    _ ≤ ε + δ := add_le_add h₁₂ h₂₃

end Approximates3

end Colored3Graph

end TauCeti
