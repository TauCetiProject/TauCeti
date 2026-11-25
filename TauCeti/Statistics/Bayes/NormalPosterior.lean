/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The posterior of a normal location

For `n` observations from `N(θ, v)` with known variance `v` and sample mean `m`, the likelihood
of the location `θ` is proportional to `exp (-n (θ - m)² / (2v))`. The posterior under a prior
density `prior` is the normalized measure with density the positive part of
`prior θ · exp (-n (θ - m)² / (2v))` with respect to Lebesgue measure. It is a probability
measure as soon as this density has a positive finite integral. For a Gaussian prior
`N(μ₀, v₀)` of variance `v₀ ≠ 0` the posterior is Gaussian, with precision
`n / v + 1 / v₀` (the sum of the precisions of the sample mean and of the prior) and the
precision-weighted mean `(n m / v + μ₀ / v₀) / (n / v + 1 / v₀)`.

## Main definitions

* `TauCeti.normalPosterior prior v n m`: the posterior of a normal location.

## Main results

* `TauCeti.isProbabilityMeasure_normalPosterior`: the posterior is a probability measure when
  the unnormalized density has positive finite integral.
* `TauCeti.normalPosterior_gaussianPDFReal`: the posterior under a Gaussian prior is Gaussian.

The definition is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Bayes/Basic.lean`.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), Example 7.2.16.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace TauCeti

/-- The **posterior of a normal location** with known variance `v`, after `n` observations with
sample mean `m`, under the prior density `prior`: the measure with density the positive part of
`prior θ · exp (-n (θ - m)² / (2v))` with respect to Lebesgue measure, divided by its total
mass. It has mass `1` exactly when that total mass is positive and finite, and is the zero
measure otherwise. Factors of the likelihood that do not depend on `θ` cancel in the
normalization. For `v = 0` the convention `n / 0 = 0` makes the likelihood constant, so the
posterior is the normalized prior. -/
def normalPosterior (prior : ℝ → ℝ) (v : ℝ≥0) (n : ℕ) (m : ℝ) : Measure ℝ :=
  let ν := volume.withDensity fun θ ↦ ENNReal.ofReal (prior θ * exp (-n * (θ - m) ^ 2 / (2 * v)))
  (ν Set.univ)⁻¹ • ν

theorem normalPosterior_def (prior : ℝ → ℝ) (v : ℝ≥0) (n : ℕ) (m : ℝ) :
    normalPosterior prior v n m =
      (∫⁻ θ, ENNReal.ofReal (prior θ * exp (-n * (θ - m) ^ 2 / (2 * v))))⁻¹ •
        volume.withDensity fun θ ↦ ENNReal.ofReal (prior θ * exp (-n * (θ - m) ^ 2 / (2 * v))) := by
  simp only [normalPosterior]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The posterior of a normal location is a probability measure when its unnormalized density
has positive finite integral. -/
theorem isProbabilityMeasure_normalPosterior {prior : ℝ → ℝ} {v : ℝ≥0} {n : ℕ} {m : ℝ}
    (h₀ : ∫⁻ θ, ENNReal.ofReal (prior θ * exp (-n * (θ - m) ^ 2 / (2 * v))) ≠ 0)
    (h_top : ∫⁻ θ, ENNReal.ofReal (prior θ * exp (-n * (θ - m) ^ 2 / (2 * v))) ≠ ∞) :
    IsProbabilityMeasure (normalPosterior prior v n m) := by
  refine ⟨?_⟩
  rw [normalPosterior_def, smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul, ENNReal.inv_mul_cancel h₀ h_top]

/-- Completing the square: the Gaussian prior density of mean `μ₀` and variance `v₀ ≠ 0` times
the normal likelihood is a positive constant times the Gaussian density with precision
`n / v + 1 / v₀` and the precision-weighted mean. -/
theorem gaussianPDFReal_mul_exp_eq_mul_gaussianPDFReal (μ₀ m : ℝ) {v₀ : ℝ≥0} (hv₀ : v₀ ≠ 0)
    (v : ℝ≥0) (n : ℕ) (θ : ℝ) :
    gaussianPDFReal μ₀ v₀ θ * exp (-n * (θ - m) ^ 2 / (2 * v)) =
      ((√(2 * π * v₀))⁻¹ * √(2 * π * ((n / v + v₀⁻¹)⁻¹ : ℝ≥0)) *
          exp (-((n / v) * (v₀ : ℝ)⁻¹ * (m - μ₀) ^ 2 / (n / v + (v₀ : ℝ)⁻¹)) / 2)) *
        gaussianPDFReal (((n : ℝ) / v * m + μ₀ / v₀) / ((n : ℝ) / v + (v₀ : ℝ)⁻¹))
          ((n / v + v₀⁻¹)⁻¹) θ := by
  set a : ℝ := n / v with ha
  have hv₀' : (v₀ : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv₀
  have hP : 0 < a + (v₀ : ℝ)⁻¹ := add_pos_of_nonneg_of_pos (by positivity)
    (inv_pos.2 (lt_of_le_of_ne v₀.coe_nonneg (Ne.symm hv₀')))
  have hσ : (((n / v + v₀⁻¹)⁻¹ : ℝ≥0) : ℝ) = (a + (v₀ : ℝ)⁻¹)⁻¹ := by push_cast; rfl
  have hs : √(2 * π * (a + (v₀ : ℝ)⁻¹)⁻¹) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by positivity) (inv_pos.2 hP))).ne'
  have hexp : exp (-(θ - μ₀) ^ 2 / (2 * v₀)) * exp (-n * (θ - m) ^ 2 / (2 * v)) =
      exp (-(a * (v₀ : ℝ)⁻¹ * (m - μ₀) ^ 2 / (a + (v₀ : ℝ)⁻¹)) / 2) *
        exp (-(θ - (a * m + μ₀ / v₀) / (a + (v₀ : ℝ)⁻¹)) ^ 2 / (2 * (a + (v₀ : ℝ)⁻¹)⁻¹)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    -- The likelihood exponent is `-a (θ - m)² / 2`, also when `v = 0`.
    have hlik : -(n : ℝ) * (θ - m) ^ 2 / (2 * v) = -(a * (θ - m) ^ 2) / 2 := by
      rw [ha]
      ring
    rw [hlik]
    have h₁ : (v₀ : ℝ) * a + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [gaussianPDFReal_def, gaussianPDFReal_def, hσ, mul_assoc, hexp]
  generalize √(2 * π * (a + (v₀ : ℝ)⁻¹)⁻¹) = S at hs ⊢
  field_simp

/-- **Conjugacy of the Gaussian prior**: under a prior `N(μ₀, v₀)` of variance `v₀ ≠ 0`, the
posterior of a normal location is Gaussian with precision `n / v + 1 / v₀` and mean
`(n m / v + μ₀ / v₀) / (n / v + 1 / v₀)`. -/
theorem normalPosterior_gaussianPDFReal (μ₀ m : ℝ) {v₀ : ℝ≥0} (hv₀ : v₀ ≠ 0) (v : ℝ≥0) (n : ℕ) :
    normalPosterior (gaussianPDFReal μ₀ v₀) v n m =
      gaussianReal (((n : ℝ) / v * m + μ₀ / v₀) / ((n : ℝ) / v + (v₀ : ℝ)⁻¹))
        ((n / v + v₀⁻¹)⁻¹) := by
  set μ₁ : ℝ := ((n : ℝ) / v * m + μ₀ / v₀) / ((n : ℝ) / v + (v₀ : ℝ)⁻¹)
  set σ : ℝ≥0 := (n / v + v₀⁻¹)⁻¹
  set C : ℝ := (√(2 * π * v₀))⁻¹ * √(2 * π * σ) *
    exp (-((n / v) * (v₀ : ℝ)⁻¹ * (m - μ₀) ^ 2 / (n / v + (v₀ : ℝ)⁻¹)) / 2)
  have hσ : σ ≠ 0 := inv_ne_zero (ne_of_gt (add_pos_of_nonneg_of_pos bot_le
    (inv_pos.2 (pos_iff_ne_zero.2 hv₀))))
  have hC : 0 < C := by
    have : 0 < v₀ := pos_iff_ne_zero.2 hv₀
    have : 0 < σ := pos_iff_ne_zero.2 hσ
    positivity
  have hν : (volume.withDensity fun θ ↦
      ENNReal.ofReal (gaussianPDFReal μ₀ v₀ θ * exp (-n * (θ - m) ^ 2 / (2 * v)))) =
      ENNReal.ofReal C • gaussianReal μ₁ σ := by
    have hpt (θ : ℝ) : ENNReal.ofReal (gaussianPDFReal μ₀ v₀ θ *
        exp (-n * (θ - m) ^ 2 / (2 * v))) = (ENNReal.ofReal C • gaussianPDF μ₁ σ) θ := by
      rw [gaussianPDFReal_mul_exp_eq_mul_gaussianPDFReal μ₀ m hv₀ v n, ENNReal.ofReal_mul hC.le,
        Pi.smul_apply, smul_eq_mul, gaussianPDF_def]
    rw [funext hpt, gaussianReal_of_var_ne_zero _ hσ,
      withDensity_smul _ (measurable_gaussianPDF _ _)]
  simp only [normalPosterior, hν]
  rw [smul_apply, measure_univ, smul_eq_mul, mul_one, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top, one_smul]

end TauCeti
