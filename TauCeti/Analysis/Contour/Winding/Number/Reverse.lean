/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Orientation reversal for contour winding numbers

This file records the basic orientation-reversal API for the generalized winding number.
Reversing the interval orientation negates the single-point Cauchy principal value defining
`Contour.windingNumber`, so the winding number itself changes sign.

These lemmas are bookkeeping for curves and cycles. Cycles are oriented formal combinations of
curves, and finite decompositions of curves into avoiding pieces and model sectors need both
concatenation and orientation reversal.

## Main results

* `Contour.windingNumber_symm` — the generalized winding number changes sign when the interval is
  reversed.
* `Contour.windingNumber_eq_zero_symm`, `Contour.IsNullHomologous.symm` — vanishing of the winding
  number, and hence null-homology, is preserved by reversing orientation.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number; no formal source is
vendored.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {Ω : Set ℂ}

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the orientation-reversal statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

/-- The generalized winding number changes sign when the interval orientation is reversed,
provided the principal value defining the original winding number exists. -/
theorem windingNumber_symm (h : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = -windingNumber γ a b z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt.symm,
    windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt]
  ring

/-- Pointwise vanishing of a winding number is preserved by reversing the interval orientation.
No existence hypothesis is needed: if the principal value does not exist, both winding numbers are
the junk value of `limUnder`. -/
theorem windingNumber_eq_zero_symm (hzero : windingNumber γ a b z₀ = 0) :
    windingNumber γ b a z₀ = 0 := by
  rw [windingNumber_eq_cauchyPVAt, mul_eq_zero] at hzero ⊢
  exact hzero.imp_right cauchyPVAt_eq_zero_symm

/-- Null-homology is preserved by reversing orientation. -/
theorem IsNullHomologous.symm (h : IsNullHomologous γ a b Ω) : IsNullHomologous γ b a Ω := by
  rw [isNullHomologous_iff] at h ⊢
  exact fun z hz ↦ windingNumber_eq_zero_symm (h z hz)

end TauCeti.Contour

end
