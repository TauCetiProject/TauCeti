/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.CauchyPrincipalValueOn
public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Degenerate intervals for contour winding numbers

This file records the identity piece for the generalized winding-number calculus.  The
concatenation and orientation-reversal API treats a curve by cutting and reorienting parameter
intervals; the zero-length interval is the corresponding neutral piece.

It provides degenerate-interval winding-number and null-homology API, together with endpoint
equality variants for transporting those results across equal parameter endpoints.

## Main results

* `Contour.windingNumber_refl` — the generalized winding number on `[a, a]` is `0`.
* `Contour.IsNullHomologous.refl` — every degenerate parameter interval is null-homologous in
  every ambient set.
* `..._of_eq` variants — the same results when the endpoint equality is available as a
  hypothesis.

These are Layer 0 bookkeeping prerequisites for the curve/cycle algebra in the
Hungerbühler--Wasem contour-integration roadmap.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {Ω : Set ℂ}

/-- The generalized winding number over a zero-length interval is `0`. -/
@[simp]
theorem windingNumber_refl (γ : ℝ → ℂ) (a : ℝ) (z₀ : ℂ) :
    windingNumber γ a a z₀ = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt
    (HasCauchyPVAt.refl γ a (fun z : ℂ => (z - z₀)⁻¹) z₀)]
  ring

/-- If the two endpoints are equal, the generalized winding number is `0`. -/
theorem windingNumber_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (z₀ : ℂ) :
    windingNumber γ a b z₀ = 0 := by
  subst b
  exact windingNumber_refl γ a z₀

/-- Every zero-length parameter interval is null-homologous in every ambient set. -/
theorem IsNullHomologous.refl (γ : ℝ → ℂ) (a : ℝ) (Ω : Set ℂ) :
    IsNullHomologous γ a a Ω := by
  rw [isNullHomologous_iff]
  intro z _hz
  exact windingNumber_refl γ a z

/-- If the two endpoints are equal, the parameter interval is null-homologous in every ambient
set. -/
theorem IsNullHomologous.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (Ω : Set ℂ) :
    IsNullHomologous γ a b Ω := by
  subst b
  exact IsNullHomologous.refl γ a Ω

end TauCeti.Contour

end
