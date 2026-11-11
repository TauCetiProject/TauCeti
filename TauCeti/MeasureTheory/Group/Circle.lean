/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Measures on the circle

This file defines the measure on `Circle` obtained from a nonnegative density on the unit circle
with respect to normalized arc length. For a circle-integrable density it is finite, and for a
measurable nonnegative density its integral is identified with Mathlib's `Real.circleAverage`.

## Main definitions and results

* `TauCeti.circleDensityMeasure`: normalized arc length weighted by a density.
* `TauCeti.isFiniteMeasure_circleDensityMeasure`: a circle-integrable density gives a finite
  measure.
* `TauCeti.integral_map_circleExp_of_restrict_Ioc`: integration against the pushforward along
  `Circle.exp` of a measure concentrated on `(a, a + 2π]`, for an arbitrary integrand.
* `TauCeti.integral_circleDensityMeasure`: for a nonnegative measurable density, integration
  against the weighted measure is a circle average.
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

/-- A measure on `Circle` given by a circle-integrable density with respect to normalized arc
length is finite. -/
theorem isFiniteMeasure_circleDensityMeasure {φ : ℂ → ℝ} (hφ : CircleIntegrable φ 0 1) :
    IsFiniteMeasure (circleDensityMeasure φ) := by
  have := isFiniteMeasure_withDensity_ofReal (hφ.1.const_mul (2 * π)⁻¹).hasFiniteIntegral
  unfold circleDensityMeasure
  infer_instance

/-- Integrating against the pushforward along `Circle.exp` of a measure on `ℝ` concentrated on an
interval `(a, a + 2π]` is integrating the composition with `Circle.exp`. No regularity is required
of the integrand `g`, since `Circle.exp` is a measurable embedding on that interval. -/
theorem integral_map_circleExp_of_restrict_Ioc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure ℝ} {a : ℝ} (hμ : μ.restrict (Ioc a (a + 2 * π)) = μ)
    (g : Circle → E) :
    ∫ z, g z ∂μ.map Circle.exp = ∫ θ, g (Circle.exp θ) ∂μ := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have hexp : Circle.exp ∘ ((↑) : Ioc a (a + 2 * π) → ℝ) =
      AddCircle.homeomorphCircle' ∘ (AddCircle.measurableEquivIoc (2 * π) a).symm := by
    funext θ
    rw [Function.comp_apply, Function.comp_apply,
      (MeasurableEquiv.symm_apply_eq _).2 (AddCircle.equivIoc_coe_eq θ.2).symm,
      AddCircle.homeomorphCircle'_apply_mk]
  have he : MeasurableEmbedding (Circle.exp ∘ ((↑) : Ioc a (a + 2 * π) → ℝ)) := hexp ▸
    AddCircle.homeomorphCircle'.toMeasurableEquiv.measurableEmbedding.comp
      (AddCircle.measurableEquivIoc (2 * π) a).symm.measurableEmbedding
  have hμ' : (μ.comap Subtype.val).map ((↑) : Ioc a (a + 2 * π) → ℝ) = μ := by
    rw [map_comap_subtype_coe measurableSet_Ioc, hμ]
  calc ∫ z, g z ∂μ.map Circle.exp
      = ∫ z, g z ∂(μ.comap Subtype.val).map (Circle.exp ∘ ((↑) : Ioc a (a + 2 * π) → ℝ)) := by
        rw [← Measure.map_map Circle.exp.continuous.measurable measurable_subtype_coe, hμ']
    _ = ∫ θ, g (Circle.exp θ) ∂(μ.comap Subtype.val).map ((↑) : Ioc a (a + 2 * π) → ℝ) := by
        rw [he.integral_map, (MeasurableEmbedding.subtype_coe measurableSet_Ioc).integral_map]
        simp only [Function.comp_apply]
    _ = ∫ θ, g (Circle.exp θ) ∂μ := by rw [hμ']

/-- Integration against a measure on `Circle` with a nonnegative almost everywhere strongly
measurable density is the corresponding normalized circle average. No regularity is required of
the integrand `g`. -/
theorem integral_circleDensityMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℂ → ℝ}
    (hφ : AEStronglyMeasurable (fun θ ↦ φ (circleMap 0 1 θ)) (volume.restrict (Ioc 0 (2 * π))))
    (hφ₀ : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ φ z) (g : ℂ → E) :
    ∫ z : Circle, g z ∂circleDensityMeasure φ = circleAverage (fun ζ ↦ φ ζ • g ζ) 0 1 := by
  have hd : AEMeasurable (fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ)))
      (volume.restrict (Ioc 0 (2 * π))) :=
    (hφ.const_mul _).aemeasurable.ennreal_ofReal
  have hν : ((volume.restrict (Ioc 0 (2 * π))).withDensity
      fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ))).restrict (Ioc 0 (0 + 2 * π)) =
      (volume.restrict (Ioc 0 (2 * π))).withDensity
        fun θ ↦ ENNReal.ofReal ((2 * π)⁻¹ * φ (circleMap 0 1 θ)) := by
    rw [zero_add, restrict_withDensity measurableSet_Ioc,
      Measure.restrict_restrict_of_subset subset_rfl]
  rw [circleDensityMeasure, integral_map_circleExp_of_restrict_Ioc hν (fun z ↦ g z),
    integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top), circleAverage_def,
    intervalIntegral.integral_of_le (by positivity), ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun θ ↦ ?_)
  have h₀ : 0 ≤ (2 * π)⁻¹ * φ (circleMap 0 1 θ) :=
    mul_nonneg (by positivity) (hφ₀ _ (circleMap_mem_sphere 0 zero_le_one θ))
  simp only [ENNReal.toReal_ofReal h₀, smul_smul]
  simp [Circle.coe_exp, circleMap]

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
