/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FoldedNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import TauCeti.Probability.Distributions.Gaussian.Moments
public import TauCeti.Probability.Distributions.NoncentralChi.Moments
import TauCeti.Probability.Distributions.Tilted

/-!
# Moments and generating functions of folded normal laws

Every real exponential moment of `foldedNormalMeasure m s` is finite, so its exponential
integrability set `integrableExpSet id` is all of `ℝ` and all `Lᵖ` and polynomial moments exist.

At positive scale `s`, decomposing `(gaussianReal m (s ^ 2)).map (|·|)` into the nonnegative and
reflected negative half-lines and applying Gaussian exponential tilting gives the closed-form
moment-generating function
`mgf id (foldedNormalMeasure m s) t = exp (m * t + s ^ 2 * t ^ 2 / 2) * Φ (m / s + s * t) +`
`exp (-m * t + s ^ 2 * t ^ 2 / 2) * Φ (-m / s + s * t)`, where `Φ = cdf (gaussianReal 0 1)`,
together with the cumulant-generating function `cgf id`.

Differentiating the moment-generating function at zero yields the elementary Gaussian mean in both
standard-cdf and error-function forms:
* `E[X] = s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * (2 * Φ (m / s) - 1)`,
* `E[X] = s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * erf (m / (√2 * s))`.

Because `|x| ^ 2 = x ^ 2`, the second raw moment is `m ^ 2 + s ^ 2` and the variance is
`m ^ 2 + s ^ 2 - E[X] ^ 2`.

## References

* F. C. Leone, L. S. Nelson, R. B. Nottingham, *The folded normal distribution*, Technometrics 3
  (1961), 543–550.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, second
  edition, Wiley, 1994, chapter 13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

variable {m s t : ℝ}

/-! ### Exponential integrability and generating functions -/

/-- Every real exponential moment of `foldedNormalMeasure m s` is integrable across all parameter
values, including on the nonpositive-scale zero branch. -/
theorem integrable_exp_mul_id_foldedNormalMeasure (m s t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (foldedNormalMeasure m s) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  exact integrable_exp_mul_id_noncentralChiMeasure 1 ‖m / s‖₊ s t

/-- The exponential-integrability domain of `foldedNormalMeasure m s` is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_foldedNormalMeasure (m s : ℝ) :
    integrableExpSet id (foldedNormalMeasure m s) = univ := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure, integrableExpSet_id_noncentralChiMeasure]

/-- Every folded normal law belongs to `Lᵖ` for all `p : ℝ≥0`. -/
theorem memLp_id_foldedNormalMeasure (m s : ℝ) (p : ℝ≥0) :
    MemLp id p (foldedNormalMeasure m s) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

/-- Every natural power is integrable under `foldedNormalMeasure m s`. -/
theorem integrable_pow_foldedNormalMeasure (m s : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (foldedNormalMeasure m s) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  exact integrable_pow_noncentralChiMeasure 1 ‖m / s‖₊ s n

/-- The moment-generating function of `foldedNormalMeasure m s` at positive scale `s`, expressed in
terms of the standard Gaussian cdf `Φ = cdf (gaussianReal 0 1)`. -/
theorem mgf_id_foldedNormalMeasure (m : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    mgf id (foldedNormalMeasure m s) t =
      exp (m * t + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (m / s + s * t) +
        exp (-(m * t) + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (-m / s + s * t) := by
  set v : ℝ≥0 := (s ^ 2).toNNReal
  have hv_coe : (v : ℝ) = s ^ 2 := coe_toNNReal _ (sq_nonneg s)
  have hv : v ≠ 0 := (Real.toNNReal_pos.2 (pow_pos hs 2)).ne'
  have hsqrt : √(v : ℝ) = s := by rw [hv_coe, sqrt_sq hs.le]
  have hneg : (gaussianReal m v).neg = gaussianReal (-m) v := by
    simpa only [Measure.neg_def] using gaussianReal_map_neg (μ := m) (v := v)
  rw [mgf, foldedNormalMeasure_of_scale_pos hs, (gaussianReal m v).map_abs_eq_restrict_add_restrict,
    hneg]
  simp only [id_eq]
  rw [integral_add_measure (integrable_exp_mul_gaussianReal t).restrict
      (integrable_exp_mul_gaussianReal t).restrict,
    setIntegral_exp_mul_gaussianReal, setIntegral_exp_mul_gaussianReal]
  have h1 : (gaussianReal (m + v * t) v).real (Ici 0) =
      cdf (gaussianReal 0 1) (m / s + s * t) := by
    have := nullSingletonClass_gaussianReal (μ := m + v * t) hv
    rw [measureReal_congr (Ioi_ae_eq_Ici (a := (0 : ℝ))).symm,
      measureReal_Ioi_gaussianReal_eq_cdf _ hv 0, sub_zero, hsqrt, hv_coe]
    congr 1
    field_simp [hs.ne']
  have h2 : (gaussianReal (-m + v * t) v).real (Ioi 0) =
      cdf (gaussianReal 0 1) (-m / s + s * t) := by
    rw [measureReal_Ioi_gaussianReal_eq_cdf _ hv 0, sub_zero, hsqrt, hv_coe]
    congr 1
    field_simp [hs.ne']
  rw [h1, h2, hv_coe, neg_mul]

/-- The moment-generating function of `foldedNormalMeasure m s` is strictly positive at every real
rate when `0 < s`. -/
theorem mgf_id_foldedNormalMeasure_pos (m : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    0 < mgf id (foldedNormalMeasure m s) t := by
  rw [mgf_id_foldedNormalMeasure m hs t]
  have h1 : 0 < exp (m * t + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (m / s + s * t) :=
    mul_pos (exp_pos _) (cdf_gaussianReal_pos 0 one_ne_zero _)
  have h2 : 0 < exp (-(m * t) + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (-m / s + s * t) :=
    mul_pos (exp_pos _) (cdf_gaussianReal_pos 0 one_ne_zero _)
  linarith

/-- The cumulant-generating function of `foldedNormalMeasure m s` at positive scale `s`. -/
theorem cgf_id_foldedNormalMeasure (m : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    cgf id (foldedNormalMeasure m s) t =
      log (exp (m * t + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (m / s + s * t) +
        exp (-(m * t) + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (-m / s + s * t)) := by
  rw [cgf, mgf_id_foldedNormalMeasure m hs t]

/-! ### Mean, second moment, and variance -/

/-- Derivative at `0` of one branch of the folded normal moment-generating function. -/
private theorem hasDerivAt_mgf_branch_zero (μ s : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ exp (μ * t + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (μ / s + s * t))
      (μ * cdf (gaussianReal 0 1) (μ / s) + s * gaussianPDFReal 0 1 (μ / s)) 0 := by
  have hexp : HasDerivAt (fun t : ℝ ↦ exp (μ * t + s ^ 2 * t ^ 2 / 2)) μ 0 := by
    convert ((((hasDerivAt_id' (0 : ℝ)).const_mul μ).fun_add
      ((((hasDerivAt_id' (0 : ℝ)).fun_pow 2).const_mul (s ^ 2)).div_const 2))).exp using 1
    simp
  have hlin : HasDerivAt (fun t : ℝ ↦ μ / s + s * t) s 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul s).const_add (μ / s)
  have hcdf : HasDerivAt (fun t : ℝ ↦ cdf (gaussianReal 0 1) (μ / s + s * t))
      (gaussianPDFReal 0 1 (μ / s) * s) 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_cdf_gaussianReal 0 one_ne_zero (μ / s + s * 0)).comp 0 hlin
  convert hexp.fun_mul hcdf using 1
  simp only [mul_zero, zero_pow two_ne_zero, zero_div, add_zero, exp_zero]
  ring

/-- The mean of `foldedNormalMeasure m s` at positive scale `s`, in terms of the standard Gaussian
cdf `Φ = cdf (gaussianReal 0 1)`. -/
theorem integral_id_foldedNormalMeasure (m : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, x ∂foldedNormalMeasure m s =
      s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * (2 * cdf (gaussianReal 0 1) (m / s) - 1) := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (foldedNormalMeasure m s)) := by simp
  have h := deriv_mgf_zero (X := id) (μ := foldedNormalMeasure m s) h0
  simp only [id_eq] at h
  have hmgf : mgf id (foldedNormalMeasure m s) = fun t ↦
      exp (m * t + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (m / s + s * t) +
        exp ((-m) * t + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) ((-m) / s + s * t) := by
    ext t
    simpa only [neg_mul] using mgf_id_foldedNormalMeasure m hs t
  have hderiv := (hasDerivAt_mgf_branch_zero m s).fun_add (hasDerivAt_mgf_branch_zero (-m) s)
  rw [hmgf, hderiv.deriv] at h
  rw [← h]
  have hneg : (-m) / s = -(m / s) := neg_div s m
  have hpdf : 2 * s * gaussianPDFReal 0 1 (m / s) =
      s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) := by
    rw [gaussianPDFReal_zero_one, sqrt_mul zero_le_two, sqrt_div zero_le_two]
    have hexp_eq : -((m / s) ^ 2 / 2) = -m ^ 2 / (2 * s ^ 2) := by
      field_simp [hs.ne']
    have h2 : (2 : ℝ) = √2 ^ 2 := (sq_sqrt zero_le_two).symm
    rw [hexp_eq]
    field_simp [(sqrt_pos.2 two_pos).ne', (sqrt_pos.2 pi_pos).ne']
    rw [← h2]
  rw [hneg, cdf_gaussianReal_zero_one_neg, gaussianPDFReal_zero_neg]
  calc
    m * cdf (gaussianReal 0 1) (m / s) + s * gaussianPDFReal 0 1 (m / s) +
        (-m * (1 - cdf (gaussianReal 0 1) (m / s)) + s * gaussianPDFReal 0 1 (m / s))
      = 2 * s * gaussianPDFReal 0 1 (m / s) + m * (2 * cdf (gaussianReal 0 1) (m / s) - 1) := by
        ring
    _ = s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) +
          m * (2 * cdf (gaussianReal 0 1) (m / s) - 1) := by rw [hpdf]

/-- Error-function form of the mean of `foldedNormalMeasure m s` at positive scale `s`. -/
theorem integral_id_foldedNormalMeasure_eq_erf (m : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, x ∂foldedNormalMeasure m s =
      s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * Real.erf (m / (√2 * s)) := by
  rw [integral_id_foldedNormalMeasure m hs, cdf_gaussianReal_zero_one, div_div, mul_comm s √2]
  ring

/-- Even raw moments of `foldedNormalMeasure m s` at positive scale coincide with those of
`gaussianReal m (s ^ 2)`. -/
theorem integral_pow_two_mul_foldedNormalMeasure_eq_integral_pow_two_mul_gaussianReal
    (m : ℝ) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫ x, x ^ (2 * n) ∂foldedNormalMeasure m s =
      ∫ x, x ^ (2 * n) ∂gaussianReal m (s ^ 2).toNNReal := by
  rw [foldedNormalMeasure_of_scale_pos hs,
    integral_map continuous_abs.measurable.aemeasurable (by fun_prop)]
  congr 1 with x
  rw [pow_mul, sq_abs, ← pow_mul]

/-- The second raw moment of `foldedNormalMeasure m s` at positive scale `s` is `m ^ 2 + s ^ 2`. -/
@[simp]
theorem integral_sq_foldedNormalMeasure (m : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, x ^ 2 ∂foldedNormalMeasure m s = m ^ 2 + s ^ 2 := by
  simpa only [mul_one, integral_sq_gaussianReal, coe_toNNReal _ (sq_nonneg s), add_comm] using
    integral_pow_two_mul_foldedNormalMeasure_eq_integral_pow_two_mul_gaussianReal m hs 1

/-- The variance of `foldedNormalMeasure m s` at positive scale `s`, in terms of the standard
Gaussian cdf `Φ = cdf (gaussianReal 0 1)`. -/
theorem variance_id_foldedNormalMeasure (m : ℝ) {s : ℝ} (hs : 0 < s) :
    variance id (foldedNormalMeasure m s) =
      m ^ 2 + s ^ 2 -
        (s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) +
          m * (2 * cdf (gaussianReal 0 1) (m / s) - 1)) ^ 2 := by
  let _ := isProbabilityMeasure_foldedNormalMeasure m hs
  rw [variance_eq_sub (memLp_id_foldedNormalMeasure m s 2)]
  simp only [Pi.pow_apply, id_eq, integral_sq_foldedNormalMeasure m hs,
    integral_id_foldedNormalMeasure m hs]

/-- Error-function form of the variance of `foldedNormalMeasure m s` at positive scale `s`. -/
theorem variance_id_foldedNormalMeasure_eq_erf (m : ℝ) {s : ℝ} (hs : 0 < s) :
    variance id (foldedNormalMeasure m s) =
      m ^ 2 + s ^ 2 -
        (s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * Real.erf (m / (√2 * s))) ^ 2 := by
  let _ := isProbabilityMeasure_foldedNormalMeasure m hs
  rw [variance_eq_sub (memLp_id_foldedNormalMeasure m s 2)]
  simp only [Pi.pow_apply, id_eq, integral_sq_foldedNormalMeasure m hs,
    integral_id_foldedNormalMeasure_eq_erf m hs]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti Real TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m s : ℝ}

/-- Every natural moment of a random variable with a folded normal law is integrable. -/
theorem integrable_pow_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_pow_foldedNormalMeasure m s n)

/-- Every real exponential moment of a random variable with a folded normal law is integrable. -/
theorem integrable_exp_mul_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) P :=
  hX.integrable_fun_comp (integrable_exp_mul_id_foldedNormalMeasure m s t)

/-- Closed-form moment-generating function of a random variable with law `foldedNormalMeasure m s`
at positive scale. -/
theorem mgf_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) (hs : 0 < s) (t : ℝ) :
    mgf X P t =
      exp (m * t + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (m / s + s * t) +
        exp (-(m * t) + s ^ 2 * t ^ 2 / 2) * cdf (gaussianReal 0 1) (-m / s + s * t) := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq, mgf_id_foldedNormalMeasure m hs t]

/-- Expectation of a random variable with law `foldedNormalMeasure m s` at positive scale, in
standard-cdf form. -/
theorem integral_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) (hs : 0 < s) :
    ∫ ω, X ω ∂P =
      s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * (2 * cdf (gaussianReal 0 1) (m / s) - 1) := by
  rw [hX.integral_eq, integral_id_foldedNormalMeasure m hs]

/-- Expectation of a random variable with law `foldedNormalMeasure m s` at positive scale, in
error-function form. -/
theorem integral_foldedNormalMeasure_eq_erf
    (hX : HasLaw X (foldedNormalMeasure m s) P) (hs : 0 < s) :
    ∫ ω, X ω ∂P =
      s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * Real.erf (m / (√2 * s)) := by
  rw [hX.integral_eq, integral_id_foldedNormalMeasure_eq_erf m hs]

/-- Second raw moment of a random variable with law `foldedNormalMeasure m s` at positive scale. -/
theorem integral_sq_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) (hs : 0 < s) :
    ∫ ω, X ω ^ 2 ∂P = m ^ 2 + s ^ 2 := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ 2), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_sq_foldedNormalMeasure m hs]

/-- Variance of a random variable with law `foldedNormalMeasure m s` at positive scale, in
standard-cdf form. -/
theorem variance_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) (hs : 0 < s) :
    variance X P =
      m ^ 2 + s ^ 2 -
        (s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) +
          m * (2 * cdf (gaussianReal 0 1) (m / s) - 1)) ^ 2 := by
  rw [hX.variance_eq, variance_id_foldedNormalMeasure m hs]

/-- Variance of a random variable with law `foldedNormalMeasure m s` at positive scale, in
error-function form. -/
theorem variance_foldedNormalMeasure_eq_erf
    (hX : HasLaw X (foldedNormalMeasure m s) P) (hs : 0 < s) :
    variance X P =
      m ^ 2 + s ^ 2 -
        (s * √(2 / π) * exp (-m ^ 2 / (2 * s ^ 2)) + m * Real.erf (m / (√2 * s))) ^ 2 := by
  rw [hX.variance_eq, variance_id_foldedNormalMeasure_eq_erf m hs]

end ProbabilityTheory.HasLaw
