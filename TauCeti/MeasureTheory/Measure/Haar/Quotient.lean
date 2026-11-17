/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-!
# Weil's formula for nonnegative functions

Let `μ` be a right-invariant measure on a group `G`, let the right action of a countable
subgroup `Γ` on `G` have a fundamental domain, and let `ν` be the quotient measure on `G ⧸ Γ`.
**Weil's formula** unfolds an integral over `G` into an integral over `G ⧸ Γ` of the sum over
each coset: `∫ f dμ = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`.

Mathlib proves this for integrable functions with values in a normed space
(`QuotientGroup.integral_eq_integral_automorphize`). This file gives the companion statement
for nonnegative measurable functions with values in `ℝ≥0∞`, which needs no integrability
hypothesis.

## Main results

* `QuotientGroup.lintegral_eq_lintegral_automorphize`: Weil's formula for nonnegative measurable
  functions.
-/

public section

open MeasureTheory

open scoped ENNReal

/-- **Weil's formula** for nonnegative measurable functions. Let `μ` be a right-invariant measure
on `G`, let the right action of a countable subgroup `Γ` on `G` have a fundamental domain, and let
`ν` be the quotient measure on `G ⧸ Γ`. Then `∫ f dμ = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`; the
inner sum is `QuotientGroup.automorphize f`, which is constant on each left coset `g Γ`. This is
the nonnegative companion of Mathlib's `QuotientGroup.integral_eq_integral_automorphize`, and
follows the same unfolding argument over a fundamental domain. -/
theorem QuotientGroup.lintegral_eq_lintegral_automorphize {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ] {μ : Measure G}
    [μ.IsMulRightInvariant] [HasFundamentalDomain Γ.op G μ] (ν : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage μ ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ x, automorphize f x ∂ν := by
  obtain ⟨s, hs⟩ := ‹HasFundamentalDomain Γ.op G μ›.ExistsIsFundamentalDomain
  have hmeas : Measurable (automorphize f : G ⧸ Γ → ℝ≥0∞) :=
    measurable_from_quotient.mpr (Measurable.tsum fun γ ↦ hf.comp (measurable_const_smul _))
  have hπ := measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage μ hs ν
  rw [← hπ.lintegral_comp hmeas, hs.lintegral_eq_tsum'' f]
  exact (lintegral_tsum fun γ ↦ (hf.comp (measurable_const_smul _)).aemeasurable).symm
