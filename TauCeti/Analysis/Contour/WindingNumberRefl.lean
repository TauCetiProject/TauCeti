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

The statements are conditional-free because an interval with equal endpoints has zero
interval integral for every truncation, and Mathlib's `IntervalIntegrable.refl` supplies the
truncated-integrability clause in the Cauchy principal-value predicate.

## Main results

* `Contour.HasCauchyPVAt.refl` — the single-point Cauchy principal value on `[a, a]` is `0`.
* `Contour.CauchyPVExistsAt.refl`, `Contour.cauchyPVAt_refl` — existence and value forms.
* `Contour.HasCauchyPV.refl`, `Contour.CauchyPVExists.refl`, `Contour.cauchyPV_refl` — the
  corresponding set-level principal-value forms.
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

/-- The Cauchy principal value at a single point over a zero-length interval is `0`.  This is the
identity piece for the single-point principal-value calculus. -/
theorem HasCauchyPVAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    HasCauchyPVAt γ a a f z₀ 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards with ε
    exact IntervalIntegrable.refl
  · simpa only [intervalIntegral.integral_same] using tendsto_const_nhds (x := (0 : ℂ))

/-- If the two endpoints are equal, the single-point Cauchy principal value is `0`. -/
theorem HasCauchyPVAt.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    HasCauchyPVAt γ a b f z₀ 0 := by
  subst b
  exact HasCauchyPVAt.refl γ a f z₀

/-- Existence form of `HasCauchyPVAt.refl`: a zero-length interval always has a single-point
Cauchy principal value. -/
theorem CauchyPVExistsAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    CauchyPVExistsAt γ a a f z₀ :=
  CauchyPVExistsAt.intro (HasCauchyPVAt.refl γ a f z₀)

/-- Existence form of `HasCauchyPVAt.of_eq`. -/
theorem CauchyPVExistsAt.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    CauchyPVExistsAt γ a b f z₀ :=
  CauchyPVExistsAt.intro (HasCauchyPVAt.of_eq γ hab f z₀)

/-- Value form of `HasCauchyPVAt.refl`: the single-point Cauchy principal value on `[a, a]` is
`0`. -/
@[simp]
theorem cauchyPVAt_refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    cauchyPVAt γ a a f z₀ = 0 :=
  (HasCauchyPVAt.refl γ a f z₀).cauchyPVAt_eq

/-- Value form of `HasCauchyPVAt.of_eq`. -/
theorem cauchyPVAt_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) (z₀ : ℂ) :
    cauchyPVAt γ a b f z₀ = 0 :=
  (HasCauchyPVAt.of_eq γ hab f z₀).cauchyPVAt_eq

/-- The set-level Cauchy principal value over a zero-length interval is `0`, witnessed by the
empty excision set. -/
theorem HasCauchyPV.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) :
    HasCauchyPV γ a a f 0 := by
  refine HasCauchyPV.intro ∅ ?_ ?_
  · filter_upwards with ε
    exact IntervalIntegrable.refl
  · simpa only [Finset.exists_mem_empty_iff, if_false, intervalIntegral.integral_same]
      using tendsto_const_nhds (x := (0 : ℂ))

/-- If the two endpoints are equal, the set-level Cauchy principal value is `0`. -/
theorem HasCauchyPV.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) :
    HasCauchyPV γ a b f 0 := by
  subst b
  exact HasCauchyPV.refl γ a f

/-- Existence form of `HasCauchyPV.refl`: a zero-length interval always has a set-level Cauchy
principal value. -/
theorem CauchyPVExists.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) :
    CauchyPVExists γ a a f :=
  CauchyPVExists.intro (HasCauchyPV.refl γ a f)

/-- Existence form of `HasCauchyPV.of_eq`. -/
theorem CauchyPVExists.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) :
    CauchyPVExists γ a b f :=
  CauchyPVExists.intro (HasCauchyPV.of_eq γ hab f)

/-- Value form of `HasCauchyPV.refl`: the set-level Cauchy principal value on `[a, a]` is `0`. -/
@[simp]
theorem cauchyPV_refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) :
    cauchyPV γ a a f = 0 :=
  (HasCauchyPV.refl γ a f).cauchyPV_eq

/-- Value form of `HasCauchyPV.of_eq`. -/
theorem cauchyPV_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (f : ℂ → ℂ) :
    cauchyPV γ a b f = 0 :=
  (HasCauchyPV.of_eq γ hab f).cauchyPV_eq

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

/-- A pointwise zero form of `windingNumber_refl`, convenient when the curve and endpoint are
implicit. -/
theorem windingNumber_eq_zero_refl :
    windingNumber γ a a z₀ = 0 :=
  windingNumber_refl γ a z₀

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

/-- A zero-length interval is null-homologous in the empty ambient set; equivalently all its winding
numbers vanish. -/
theorem isNullHomologous_empty_refl (γ : ℝ → ℂ) (a : ℝ) :
    IsNullHomologous γ a a (∅ : Set ℂ) :=
  IsNullHomologous.refl γ a ∅

end TauCeti.Contour

end
