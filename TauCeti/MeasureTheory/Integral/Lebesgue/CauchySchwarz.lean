/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Cauchy–Schwarz inequality for lower Lebesgue integrals

This file proves the pointwise-dominated Cauchy–Schwarz inequality for extended nonnegative
Lebesgue integrals: if h x ^ 2 ≤ f x * g x almost everywhere, then
(∫⁻ x, h x ∂μ) ^ 2 ≤ (∫⁻ x, f x ∂μ) * (∫⁻ x, g x ∂μ), together with the direct product and
unit-weight corollaries.

## Main results

* TauCeti.sq_lintegral_le: if h ^ 2 ≤ f * g almost everywhere and , g are a.e. measurable,
  then (∫⁻ x, h x ∂μ) ^ 2 ≤ (∫⁻ x, f x ∂μ) * (∫⁻ x, g x ∂μ).
* TauCeti.sq_lintegral_mul_le: (∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * (∫⁻ x, g x ^ 2 ∂μ).
* TauCeti.sq_lintegral_le_mul_measure_univ:
  (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * μ Set.univ.

## Provenance

Generalized from New.sq_lintegral_le in src/Lib/General/Measure/IdempotentKernel.lean of
[grh-lean](https://github.com/lsernau/grh-lean) at commit
72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open MeasureTheory ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy–Schwarz inequality for lower Lebesgue integrals: if  and g are almost everywhere
measurable and h x ^ 2 ≤ f x * g x almost everywhere, then
(∫⁻ x, h x ∂μ) ^ 2 ≤ (∫⁻ x, f x ∂μ) * (∫⁻ x, g x ∂μ). -/
theorem sq_lintegral_le {f g h : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h_sq : ∀ᵐ x ∂μ, h x ^ 2 ≤ f x * g x) :
    (∫⁻ x, h x ∂μ) ^ 2 ≤ (∫⁻ x, f x ∂μ) * ∫⁻ x, g x ∂μ := by
  have h_iff (a b c : ℝ≥0∞) : a ^ 2 ≤ b * c ↔ a ≤ b ^ (2 : ℝ)⁻¹ * c ^ (2 : ℝ)⁻¹ := by
    simp [← mul_rpow_of_nonneg, le_rpow_inv_iff]
  rw [h_iff]
  calc ∫⁻ x, h x ∂μ
      ≤ ∫⁻ x, f x ^ (2 : ℝ)⁻¹ * g x ^ (2 : ℝ)⁻¹ ∂μ :=
        lintegral_mono_ae (h_sq.mono fun x hx ↦ (h_iff (h x) (f x) (g x)).mp hx)
    _ ≤ (∫⁻ x, f x ∂μ) ^ (2 : ℝ)⁻¹ * (∫⁻ x, g x ∂μ) ^ (2 : ℝ)⁻¹ :=
        lintegral_mul_norm_pow_le hf hg (by simp) (by simp) (by norm_num)

/-- Cauchy–Schwarz inequality for the lower Lebesgue integral of a product:
(∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * (∫⁻ x, g x ^ 2 ∂μ). -/
theorem sq_lintegral_mul_le {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * ∫⁻ x, g x ^ 2 ∂μ :=
  sq_lintegral_le (hf.pow_const 2) (hg.pow_const 2) (.of_forall fun x ↦ by rw [mul_pow])

/-- Cauchy–Schwarz inequality against the total measure:
(∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * μ Set.univ. -/
theorem sq_lintegral_le_mul_measure_univ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * μ Set.univ := by
  simpa using sq_lintegral_mul_le hf (aemeasurable_const (b := (1 : ℝ≥0∞)))

end TauCeti
