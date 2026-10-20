/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Normalized weighted laws

For a measure `μ` and a weight `w : α → ℝ≥0∞`, the normalized weighted law reweights `μ` by the
density `w` and normalizes the result:

  `μ.normalizedWithDensity w = (∫⁻ x, w x ∂μ)⁻¹ • μ.withDensity w`.

The normalizing constant is taken in `ℝ≥0∞`, so the expression is totalized: when `w` has zero or
infinite integral the result is the zero measure. In particular the law is always either zero or a
probability measure. Power biasing (`MeasureTheory.Measure.powerBias`) and size biasing are the
special cases `w x = x ^ q` and `w x = x`.

The construction follows Mathlib's exponential tilting `MeasureTheory.Measure.tilted`, which is the
case `w = exp ∘ f`, normalized in `ℝ` rather than in `ℝ≥0∞`.

## Main definitions

* `MeasureTheory.Measure.normalizedWithDensity` — the law `μ` reweighted by `w`, normalized.

## Main results

* `MeasureTheory.Measure.normalizedWithDensity_apply` and
  `MeasureTheory.Measure.rnDeriv_normalizedWithDensity` — the masses of the law and its density
  `w / ∫ w` with respect to `μ`;
* `MeasureTheory.Measure.normalizedWithDensity_eq_zero_iff` — the law is zero exactly when `w` has
  zero or infinite integral;
* `MeasureTheory.Measure.isZeroOrProbabilityMeasure_normalizedWithDensity` and
  `MeasureTheory.Measure.isProbabilityMeasure_normalizedWithDensity` — the law is always zero or a
  probability measure, and it is a probability measure when `w` has positive finite integral;
* `MeasureTheory.Measure.lintegral_normalizedWithDensity` — integration against the law is
  integration of `w * g` against `μ`, normalized;
* `MeasureTheory.Measure.normalizedWithDensity_eq_of_withDensity_eq_smul` — a probability measure
  that is a positive finite multiple of `μ.withDensity w` is the normalized weighted law.
-/

public section

noncomputable section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {w : α → ℝ≥0∞}

/-- The law `μ` reweighted by the density `w` and normalized to total mass one. The normalization
is taken in `ℝ≥0∞`, so the result is the zero measure when `w` has zero or infinite integral
against `μ`. -/
def normalizedWithDensity (μ : Measure α) (w : α → ℝ≥0∞) : Measure α :=
  (∫⁻ x, w x ∂μ)⁻¹ • μ.withDensity w

/-- Unfolding lemma for `MeasureTheory.Measure.normalizedWithDensity`. -/
theorem normalizedWithDensity_def (μ : Measure α) (w : α → ℝ≥0∞) :
    μ.normalizedWithDensity w = (∫⁻ x, w x ∂μ)⁻¹ • μ.withDensity w := by
  rw [normalizedWithDensity]

/-- The normalized weighted law of the zero measure is zero. -/
@[simp]
theorem normalizedWithDensity_zero_measure (w : α → ℝ≥0∞) :
    (0 : Measure α).normalizedWithDensity w = 0 := by
  simp [normalizedWithDensity_def]

/-- The mass of a measurable set under the normalized weighted law. -/
theorem normalizedWithDensity_apply (μ : Measure α) (w : α → ℝ≥0∞) {s : Set α}
    (hs : MeasurableSet s) :
    μ.normalizedWithDensity w s = (∫⁻ x, w x ∂μ)⁻¹ * ∫⁻ x in s, w x ∂μ := by
  rw [normalizedWithDensity_def, smul_apply, withDensity_apply _ hs, smul_eq_mul]

/-- The total mass of the normalized weighted law. -/
theorem normalizedWithDensity_apply_univ (μ : Measure α) (w : α → ℝ≥0∞) :
    μ.normalizedWithDensity w univ = (∫⁻ x, w x ∂μ)⁻¹ * ∫⁻ x, w x ∂μ := by
  rw [normalizedWithDensity_apply _ _ MeasurableSet.univ, setLIntegral_univ]

/-- A weight with zero integral gives the zero law. -/
theorem normalizedWithDensity_of_lintegral_eq_zero (h : ∫⁻ x, w x ∂μ = 0) :
    μ.normalizedWithDensity w = 0 := by
  rw [← measure_univ_eq_zero, normalizedWithDensity_apply_univ, h, mul_zero]

/-- A weight with infinite integral gives the zero law. -/
theorem normalizedWithDensity_of_lintegral_eq_top (h : ∫⁻ x, w x ∂μ = ∞) :
    μ.normalizedWithDensity w = 0 := by
  rw [normalizedWithDensity_def, h, ENNReal.inv_top, zero_smul]

/-- A weight with positive finite integral gives a probability measure. -/
theorem isProbabilityMeasure_normalizedWithDensity (h0 : ∫⁻ x, w x ∂μ ≠ 0)
    (htop : ∫⁻ x, w x ∂μ ≠ ∞) : IsProbabilityMeasure (μ.normalizedWithDensity w) :=
  ⟨by rw [normalizedWithDensity_apply_univ, ENNReal.inv_mul_cancel h0 htop]⟩

/-- The normalized weighted law is zero exactly when the weight has zero or infinite integral. -/
theorem normalizedWithDensity_eq_zero_iff :
    μ.normalizedWithDensity w = 0 ↔ ∫⁻ x, w x ∂μ = 0 ∨ ∫⁻ x, w x ∂μ = ∞ := by
  refine ⟨fun h => ?_, fun h => h.elim normalizedWithDensity_of_lintegral_eq_zero
    normalizedWithDensity_of_lintegral_eq_top⟩
  by_contra! hw
  have := isProbabilityMeasure_normalizedWithDensity hw.1 hw.2
  exact IsProbabilityMeasure.ne_zero _ h

/-- A normalized weighted law is either zero or a probability measure. -/
instance isZeroOrProbabilityMeasure_normalizedWithDensity (μ : Measure α) (w : α → ℝ≥0∞) :
    IsZeroOrProbabilityMeasure (μ.normalizedWithDensity w) := by
  by_cases h : ∫⁻ x, w x ∂μ = 0 ∨ ∫⁻ x, w x ∂μ = ∞
  · rw [normalizedWithDensity_eq_zero_iff.2 h]
    infer_instance
  · have := isProbabilityMeasure_normalizedWithDensity (not_or.1 h).1 (not_or.1 h).2
    infer_instance

/-- A normalized weighted law is absolutely continuous with respect to the original law. -/
theorem normalizedWithDensity_absolutelyContinuous (μ : Measure α) (w : α → ℝ≥0∞) :
    μ.normalizedWithDensity w ≪ μ :=
  (withDensity_absolutelyContinuous _ _).smul_left _

/-- The Radon–Nikodym derivative of the normalized weighted law with respect to the original law
is the normalized weight. -/
theorem rnDeriv_normalizedWithDensity (μ : Measure α) [SigmaFinite μ] (hw : Measurable w)
    (hw_top : ∀ᵐ x ∂μ, w x ≠ ∞) :
    (μ.normalizedWithDensity w).rnDeriv μ =ᵐ[μ] fun x => (∫⁻ y, w y ∂μ)⁻¹ * w x := by
  rcases eq_or_ne (∫⁻ x, w x ∂μ) 0 with hZ | hZ
  · have h0 := (lintegral_eq_zero_iff hw).1 hZ
    rw [normalizedWithDensity_of_lintegral_eq_zero hZ]
    filter_upwards [rnDeriv_zero μ, h0] with x hx hx0
    rw [hx, Pi.zero_apply, hx0, Pi.zero_apply, mul_zero]
  · have := SigmaFinite.withDensity_of_ne_top hw_top
    rw [normalizedWithDensity_def]
    filter_upwards [rnDeriv_smul_left_of_ne_top' (μ.withDensity w) μ (ENNReal.inv_ne_top.2 hZ),
      rnDeriv_withDensity μ hw] with x hx hx'
    rw [hx, Pi.smul_apply, hx', smul_eq_mul]

/-- Integration of a nonnegative function against the normalized weighted law. -/
theorem lintegral_normalizedWithDensity (μ : Measure α) (hw : Measurable w)
    (hw_top : ∀ᵐ x ∂μ, w x ≠ ∞) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂μ.normalizedWithDensity w = (∫⁻ x, w x ∂μ)⁻¹ * ∫⁻ x, w x * g x ∂μ := by
  rw [normalizedWithDensity_def, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hw
      (hw_top.mono fun _ h => lt_top_iff_ne_top.2 h), smul_eq_mul]
  simp only [Pi.mul_apply]

/-- If reweighting `μ` by `w` gives a positive finite multiple of a probability measure `ν`, then
`ν` is the normalized weighted law. -/
theorem normalizedWithDensity_eq_of_withDensity_eq_smul {ν : Measure α} [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : μ.withDensity w = c • ν) :
    μ.normalizedWithDensity w = ν := by
  have hZ : ∫⁻ x, w x ∂μ = c := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, h, smul_apply,
      measure_univ, smul_eq_mul, mul_one]
  rw [normalizedWithDensity_def, hZ, h, smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]

end MeasureTheory.Measure
