/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Probability.Distributions.Chi.Gaussian
import TauCeti.Probability.Distributions.Chi.Moments
import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Moments of the real Gaussian distribution

This file computes the centered moments of a variable `X` with Mathlib's real Gaussian law
`gaussianReal m v`: the absolute moments `E|X - m|ⁿ`, the even moments
`E (X - m)²ⁿ = vⁿ (2n - 1)‼`, and the vanishing of the odd ones. These closed forms are what
moment-based arguments about Gaussian variables consume, for instance Kolmogorov-type continuity
bounds and quadratic-variation estimates for Brownian increments, the half-normal mean
`E|X - m| = √(2v/π)`, and comparisons with the moments of other laws.

The absolute centered moment is obtained by folding. For positive variance `v`, after centering,
`|X - m|` has the half-normal law `chiMeasure 1 √v`, whose moments are known; for `v = 0` the
folded law is the point mass at `0`. The even centered moments follow from this formula, and the
odd ones vanish because a centered Gaussian law is symmetric.

The formulas follow the standard calculation in, for example, Johnson, Kotz, and Balakrishnan,
*Continuous Univariate Distributions*, volume 1, Chapter 13.

## Main results

* `integral_abs_sub_pow_gaussianReal` evaluates every absolute centered moment.
* `integral_sub_pow_two_mul_gaussianReal` and `centralMoment_id_two_mul_gaussianReal` evaluate
  the even centered moments.
* `integral_sub_pow_two_mul_add_one_gaussianReal` and
  `centralMoment_id_two_mul_add_one_gaussianReal` say that every odd centered moment vanishes.
* `integral_sq_gaussianReal` evaluates the second raw moment.
* `integrable_abs_gaussianReal` and `integrable_abs_add_abs_gaussianReal` give absolute
  first-moment integrability for one or two Gaussian coordinates.
-/

public section

open scoped Nat NNReal Real

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

/-- The absolute value is integrable under every real Gaussian law. -/
theorem integrable_abs_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x|) (gaussianReal μ v) := by
  have h := ((memLp_id_gaussianReal' (μ := μ) (v := v) 1 (by simp)).integrable le_rfl).norm
  simpa using h

/-- The sum of the absolute coordinate values is integrable under two real Gaussian laws. -/
theorem integrable_abs_add_abs_gaussianReal (μ₁ μ₂ : ℝ) (v₁ v₂ : ℝ≥0) :
    Integrable (fun p : ℝ × ℝ => |p.1| + |p.2|)
      (Measure.prod (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂)) :=
  ((integrable_abs_gaussianReal μ₁ v₁).comp_fst _).add
    ((integrable_abs_gaussianReal μ₂ v₂).comp_snd _)

/-- The `n`th absolute centered moment of a real Gaussian distribution. -/
@[simp]
theorem integral_abs_sub_pow_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    ∫ x, |x - m| ^ n ∂gaussianReal m v =
      (2 * (v : ℝ)) ^ ((n : ℝ) / 2) * Gamma (((n : ℝ) + 1) / 2) / √π := by
  rcases eq_or_ne v 0 with rfl | hv
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one,
        CharP.cast_eq_zero, zero_div, Real.rpow_zero, zero_add, one_mul]
      rw [Real.Gamma_one_half_eq, div_self (Real.sqrt_ne_zero'.mpr pi_pos)]
    · simp [gaussianReal_zero_var, hn.ne']
  -- Centering and folding send `gaussianReal m v` to the half-normal law `chiMeasure 1 √v`.
  calc
    _ = ∫ x, x ^ n ∂((gaussianReal m v).map (· - m)).map (|·|) := by
      rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x, x ^ n ∂chiMeasure 1 √(v : ℝ) := by
      rw [gaussianReal_map_sub_const, sub_self, gaussianReal_map_abs hv]
    _ = _ := by
      rw [integral_pow_chiMeasure one_pos (by positivity), Real.Gamma_one_half_eq,
        Real.mul_rpow zero_le_two v.coe_nonneg, Real.rpow_div_two_eq_sqrt _ v.coe_nonneg,
        Real.rpow_natCast, add_comm (1 : ℝ)]
      ring

/-- The mean of the absolute value of a centered real Gaussian, the half-normal mean:
`E|X| = √(2 * v / π)` for `X ∼ N(0, v)`. -/
theorem integral_abs_gaussianReal (v : ℝ≥0) : ∫ x, |x| ∂gaussianReal 0 v = √(2 * v / π) := by
  have h := integral_abs_sub_pow_gaussianReal 0 v 1
  simp only [sub_zero, pow_one, Nat.cast_one] at h
  rw [h, show ((1 : ℝ) + 1) / 2 = 1 by norm_num, Gamma_one, mul_one, ← sqrt_eq_rpow,
    sqrt_div' _ pi_pos.le]

/-- The integral of the `2n`th power about the mean of a real Gaussian distribution is
`vⁿ (2n - 1)‼`. -/
@[simp]
theorem integral_sub_pow_two_mul_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    (∫ x, (x - m) ^ (2 * n) ∂gaussianReal m v) =
      (v : ℝ) ^ n * (2 * n - 1 : ℕ)‼ := by
  have h := integral_abs_sub_pow_gaussianReal m v (2 * n)
  simp only [pow_abs_two_mul] at h
  rw [h]
  have hhalf_even : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by norm_num
  have hhalf_succ : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  rw [hhalf_even, Real.rpow_natCast, hhalf_succ, Real.Gamma_nat_add_half]
  field_simp [Real.sqrt_ne_zero'.mpr pi_pos]
  simp only [mul_pow]

/-- The `n`th centered moment of `gaussianReal m v` is the integral of `(x - m) ^ n`. -/
theorem centralMoment_id_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id n (gaussianReal m v) = ∫ x, (x - m) ^ n ∂gaussianReal m v := by
  simp only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq, integral_id_gaussianReal]

/-- The `2n`th centered moment of a real Gaussian distribution is
`vⁿ (2n - 1)‼`. -/
@[simp]
theorem centralMoment_id_two_mul_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (gaussianReal m v) =
      (v : ℝ) ^ n * (2 * n - 1 : ℕ)‼ := by
  rw [centralMoment_id_gaussianReal, integral_sub_pow_two_mul_gaussianReal]

/-- The second moment of a real Gaussian distribution is its variance plus its squared mean. -/
theorem integral_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂gaussianReal m v = v + m ^ 2 := by
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := m) (v := v) 2 ENNReal.ofNat_ne_top)
  rw [variance_id_gaussianReal] at h
  simp only [id_eq, Pi.pow_apply, integral_id_gaussianReal] at h
  linarith

/-- The fourth centered moment of a real Gaussian distribution is three times its
squared variance. -/
theorem integral_sub_pow_four_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ x, (x - m) ^ 4 ∂gaussianReal m v = 3 * (v : ℝ) ^ 2 := by
  have hfour : (2 * 2 - 1 : ℕ)‼ = 3 := by norm_num [Nat.doubleFactorial]
  simpa only [hfour, Nat.reduceMul, Nat.cast_ofNat, mul_comm] using
    integral_sub_pow_two_mul_gaussianReal m v 2

/-- Every odd power about the mean integrates to zero under a real Gaussian distribution. -/
@[simp]
theorem integral_sub_pow_two_mul_add_one_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    ∫ x, (x - m) ^ (2 * n + 1) ∂gaussianReal m v = 0 := by
  simpa only [id_eq, integral_id_gaussianReal] using
    IsGaussian.integral_comp_sub_eq_zero_of_odd (gaussianReal m v)
      (f := fun x : ℝ ↦ x ^ (2 * n + 1)) (odd_two_mul_add_one n).neg_pow

/-- Every odd centered moment of a real Gaussian distribution vanishes. -/
@[simp]
theorem centralMoment_id_two_mul_add_one_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n + 1) (gaussianReal m v) = 0 := by
  rw [centralMoment_id_gaussianReal, integral_sub_pow_two_mul_add_one_gaussianReal]

end TauCeti.Probability
