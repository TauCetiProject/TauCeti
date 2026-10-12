/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Measures on the circle

This file defines the measure on `Circle` obtained from a continuous nonnegative density on the
unit circle with respect to normalized arc length. Its integral is identified with Mathlib's
`Real.circleAverage`.

## Main definitions and results

* `TauCeti.circleDensityMeasure`: normalized arc length weighted by a density.
* `TauCeti.isFiniteMeasure_circleDensityMeasure`: a continuous density gives a finite measure.
* `TauCeti.integral_circleDensityMeasure`: integration against the weighted measure is a circle
  average.
* `TauCeti.circleAverage_sub_zpow`: the circle average of `(z - c) ^ n` is `1` for `n = 0` and
  `0` otherwise, the orthogonality relation of the characters of the circle.
-/

public section

noncomputable section

open Complex MeasureTheory Metric Real Set Filter
open scoped ENNReal

namespace TauCeti

/-- The measure on `Circle` with density `max φ 0` with respect to normalized arc length.

Negative values of `φ` are truncated to `0` by `ENNReal.ofReal`; for a nonnegative `φ` the density
is `φ` itself. -/
def circleDensityMeasure (φ : ℂ → ℝ) : Measure Circle :=
  ((volume.restrict (Ioc 0 (2 * π))).withDensity
    fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ))).map Circle.exp

private lemma continuous_comp_circleMap {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1)) :
    Continuous fun θ ↦ φ (circleMap 0 1 θ) :=
  hφ.comp_continuous (continuous_circleMap 0 1) fun θ ↦ circleMap_mem_sphere 0 zero_le_one θ

/-- A measure on `Circle` given by a continuous density with respect to normalized arc length is
finite. -/
theorem isFiniteMeasure_circleDensityMeasure {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (sphere 0 1)) : IsFiniteMeasure (circleDensityMeasure φ) := by
  have hint : IntegrableOn (fun θ ↦ (2 * π)⁻¹ * φ (circleMap 0 1 θ)) (Ioc 0 (2 * π)) :=
    ((continuous_const.mul (continuous_comp_circleMap hφ)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have := isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  unfold circleDensityMeasure
  infer_instance

/-- Integration against a continuous nonnegative density on `Circle` is the corresponding
normalized circle average. -/
theorem integral_circleDensityMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere 0 1))
    (hφ₀ : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ φ z) {g : ℂ → E} (hg : ContinuousOn g (sphere 0 1)) :
    ∫ z : Circle, g z ∂circleDensityMeasure φ = circleAverage (fun ζ ↦ φ ζ • g ζ) 0 1 := by
  have hgc : Continuous fun z : Circle ↦ g z :=
    hg.comp_continuous continuous_subtype_val fun z ↦ by simp
  have hexp : ∀ θ : ℝ, (Circle.exp θ : ℂ) = circleMap 0 1 θ := fun θ ↦ by
    simp [Circle.coe_exp, circleMap]
  have hmeas : Measurable fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ)) :=
    (continuous_const.mul (continuous_comp_circleMap hφ)).measurable.ennreal_ofReal
  rw [circleDensityMeasure, integral_map Circle.exp.continuous.aemeasurable
    hgc.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hmeas
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top), circleAverage_def,
    intervalIntegral.integral_of_le (by positivity), ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun θ ↦ ?_)
  have h₀ : 0 ≤ (2 * π)⁻¹ * φ (circleMap 0 1 θ) :=
    mul_nonneg (by positivity) (hφ₀ _ (circleMap_mem_sphere 0 zero_le_one θ))
  simp only [hexp, ENNReal.toReal_ofReal h₀, smul_smul]

/-- **Orthogonality of the characters of the circle.** The normalized circle average of an
integer power `(z - c) ^ n` over a circle centred at `c` is `1` for `n = 0` and `0` otherwise. -/
@[simp] theorem circleAverage_sub_zpow {c : ℂ} {R : ℝ} (n : ℤ) :
    circleAverage (fun z ↦ (z - c) ^ n) c R = if n = 0 then 1 else 0 := by
  by_cases hR : R = 0
  · subst R
    simp only [circleAverage_zero, sub_self, zero_zpow_eq]
  split_ifs with hn
  · simp [hn, circleAverage_const]
  rw [← circleAverage_abs_radius, circleAverage_eq_circleIntegral (abs_ne_zero.mpr hR),
    circleIntegral.integral_congr (abs_nonneg R) (g := fun z ↦ (z - c) ^ (n - 1)) fun z hz ↦ ?_,
    circleIntegral.integral_sub_zpow_of_ne (by omega), smul_zero]
  have hz : z - c ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hz (abs_ne_zero.mpr hR))
  simp [zpow_sub_one₀ hz, mul_comm]

end TauCeti
