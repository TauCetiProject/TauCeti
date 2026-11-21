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
density `prior` is the normalized measure with density `prior θ · exp (-n (θ - m)² / (2v))` with
respect to Lebesgue measure. It is a probability measure as soon as this density has a positive
finite integral. For a Gaussian prior `N(μ₀, τ²)` the posterior is Gaussian, with precision
`n / v + 1 / τ²` (the sum of the precisions of the sample mean and of the prior) and the
precision-weighted mean `(n m / v + μ₀ / τ²) / (n / v + 1 / τ²)`.

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
sample mean `m`, under the prior density `prior`: the measure with density
`prior θ · exp (-n (θ - m)² / (2v))` with respect to Lebesgue measure, normalized to total
mass `1`. Factors of the likelihood that do not depend on `θ` cancel in the normalization. -/
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

/-- Completing the square: a Gaussian prior density times the normal likelihood is a positive
constant times the Gaussian density with precision `n / v + 1 / τ²` and the precision-weighted
mean. -/
theorem gaussianPDFReal_mul_exp_eq_mul_gaussianPDFReal (μ₀ m : ℝ) {τ : ℝ≥0} (hτ : τ ≠ 0)
    (v : ℝ≥0) (n : ℕ) (θ : ℝ) :
    gaussianPDFReal μ₀ τ θ * exp (-n * (θ - m) ^ 2 / (2 * v)) =
      ((√(2 * π * τ))⁻¹ * √(2 * π * ((n / v + τ⁻¹)⁻¹ : ℝ≥0)) *
          exp (-((n / v) * (τ : ℝ)⁻¹ * (m - μ₀) ^ 2 / (n / v + (τ : ℝ)⁻¹)) / 2)) *
        gaussianPDFReal (((n : ℝ) / v * m + μ₀ / τ) / ((n : ℝ) / v + (τ : ℝ)⁻¹))
          ((n / v + τ⁻¹)⁻¹) θ := by
  set a : ℝ := n / v with ha
  have hτ' : (τ : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hτ
  have hP : 0 < a + (τ : ℝ)⁻¹ := add_pos_of_nonneg_of_pos (by positivity)
    (inv_pos.2 (lt_of_le_of_ne τ.coe_nonneg (Ne.symm hτ')))
  have hσ : (((n / v + τ⁻¹)⁻¹ : ℝ≥0) : ℝ) = (a + (τ : ℝ)⁻¹)⁻¹ := by push_cast; rfl
  have hs : √(2 * π * (a + (τ : ℝ)⁻¹)⁻¹) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by positivity) (inv_pos.2 hP))).ne'
  have hexp : exp (-(θ - μ₀) ^ 2 / (2 * τ)) * exp (-n * (θ - m) ^ 2 / (2 * v)) =
      exp (-(a * (τ : ℝ)⁻¹ * (m - μ₀) ^ 2 / (a + (τ : ℝ)⁻¹)) / 2) *
        exp (-(θ - (a * m + μ₀ / τ) / (a + (τ : ℝ)⁻¹)) ^ 2 / (2 * (a + (τ : ℝ)⁻¹)⁻¹)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    -- The likelihood exponent is `-a (θ - m)² / 2`, also when `v = 0`.
    have hlik : -(n : ℝ) * (θ - m) ^ 2 / (2 * v) = -(a * (θ - m) ^ 2) / 2 := by
      rw [ha]
      ring
    rw [hlik]
    have h₁ : (τ : ℝ) * a + 1 ≠ 0 := by positivity
    field_simp
    ring
  simp only [gaussianPDFReal, hσ, mul_assoc, hexp]
  rw [mul_assoc 2 π] at hs
  rw [mul_left_comm (√_) (rexp _), ← mul_assoc (√_), mul_inv_cancel₀ hs, one_mul]

/-- **Conjugacy of the Gaussian prior**: under a prior `N(μ₀, τ²)` with `τ² ≠ 0`, the posterior
of a normal location is Gaussian with precision `n / v + 1 / τ²` and mean
`(n m / v + μ₀ / τ²) / (n / v + 1 / τ²)`. -/
theorem normalPosterior_gaussianPDFReal (μ₀ m : ℝ) {τ : ℝ≥0} (hτ : τ ≠ 0) (v : ℝ≥0) (n : ℕ) :
    normalPosterior (gaussianPDFReal μ₀ τ) v n m =
      gaussianReal (((n : ℝ) / v * m + μ₀ / τ) / ((n : ℝ) / v + (τ : ℝ)⁻¹))
        ((n / v + τ⁻¹)⁻¹) := by
  set μ₁ : ℝ := ((n : ℝ) / v * m + μ₀ / τ) / ((n : ℝ) / v + (τ : ℝ)⁻¹)
  set σ : ℝ≥0 := (n / v + τ⁻¹)⁻¹
  set C : ℝ := (√(2 * π * τ))⁻¹ * √(2 * π * σ) *
    exp (-((n / v) * (τ : ℝ)⁻¹ * (m - μ₀) ^ 2 / (n / v + (τ : ℝ)⁻¹)) / 2)
  have hσ : σ ≠ 0 := inv_ne_zero (ne_of_gt (add_pos_of_nonneg_of_pos bot_le
    (inv_pos.2 (pos_iff_ne_zero.2 hτ))))
  have hC : 0 < C := by
    have : 0 < τ := pos_iff_ne_zero.2 hτ
    have : 0 < σ := pos_iff_ne_zero.2 hσ
    positivity
  have hν : (volume.withDensity fun θ ↦
      ENNReal.ofReal (gaussianPDFReal μ₀ τ θ * exp (-n * (θ - m) ^ 2 / (2 * v)))) =
      ENNReal.ofReal C • gaussianReal μ₁ σ := by
    have hpt (θ : ℝ) : ENNReal.ofReal (gaussianPDFReal μ₀ τ θ *
        exp (-n * (θ - m) ^ 2 / (2 * v))) = (ENNReal.ofReal C • gaussianPDF μ₁ σ) θ := by
      rw [gaussianPDFReal_mul_exp_eq_mul_gaussianPDFReal μ₀ m hτ v n, ENNReal.ofReal_mul hC.le]
      rfl
    rw [funext hpt, gaussianReal_of_var_ne_zero _ hσ,
      withDensity_smul _ (measurable_gaussianPDF _ _)]
  simp only [normalPosterior, hν]
  rw [smul_apply, measure_univ, smul_eq_mul, mul_one, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top, one_smul]

end TauCeti
