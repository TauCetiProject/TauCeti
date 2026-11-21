/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Probability.Moments.Pi
import TauCeti.Analysis.SpecialFunctions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Moments of the real Gaussian distribution

This file computes the centered moments of Mathlib's real Gaussian measure.  The absolute
centered moment is evaluated first from the Gaussian density and the half-line Gamma integral
`TauCeti.integral_Ioi_pow_mul_exp_neg_mul_sq`; the even centered moments follow from this
formula, and the odd ones vanish because a centered Gaussian law is symmetric.

The formulas follow the standard calculation in, for example, Johnson, Kotz, and Balakrishnan,
*Continuous Univariate Distributions*, volume 1, Chapter 13.

## Main results

* `integral_abs_sub_pow_gaussianReal` evaluates every absolute centered moment.
* `centralMoment_id_two_mul_gaussianReal` evaluates the even centered moments.
* `TauCeti.integral_exp_mul_dotProduct_pi_gaussianReal` evaluates the exponential moment of a
  linear form `y ⬝ᵥ g` on a finite product of independent real Gaussian laws.
* `centralMoment_id_two_mul_add_one_gaussianReal` says that every odd centered moment vanishes.
* `integral_sq_gaussianReal` evaluates the second raw moment.
* `integrable_abs_gaussianReal` and `integrable_abs_add_abs_gaussianReal` give absolute
  first-moment integrability for one or two Gaussian coordinates.
-/

public section

open scoped Nat NNReal Real

namespace TauCeti.Probability

open MeasureTheory ProbabilityTheory Real

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
  calc
    _ = ∫ x, |x| ^ n ∂(gaussianReal m v).map (fun x ↦ x - m) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x, |x| ^ n ∂gaussianReal 0 v := by simp [gaussianReal_map_sub_const]
    _ = ∫ x, gaussianPDFReal 0 v x * |x| ^ n :=
      integral_gaussianReal_eq_integral_smul hv
    _ = (√(2 * π * (v : ℝ)))⁻¹ *
        ∫ x : ℝ, |x| ^ n * exp (-(2 * (v : ℝ))⁻¹ * |x| ^ 2) := by
      rw [← integral_const_mul]
      congr with x
      simp only [gaussianPDFReal, sub_zero, sq_abs, div_eq_inv_mul, neg_mul, mul_neg]
      ring
    -- Fold the even integrand onto `(0, ∞)` and evaluate the half-line Gamma integral.
    _ = (√(2 * π * (v : ℝ)))⁻¹ * (2 * (Gamma (((n : ℝ) + 1) / 2) /
        (2 * ((2 * (v : ℝ))⁻¹) ^ (((n : ℝ) + 1) / 2)))) := by
      rw [integral_comp_abs (f := fun x ↦ x ^ n * exp (-(2 * (v : ℝ))⁻¹ * x ^ 2)),
        TauCeti.integral_Ioi_pow_mul_exp_neg_mul_sq (by positivity)]
    _ = _ := by
      -- Split `(2v) ^ ((n + 1) / 2)` and `√(2πv)` so that the factor `√(2v)` cancels.
      have hsplit : (2 * (v : ℝ)) ^ (((n : ℝ) + 1) / 2) =
          (2 * (v : ℝ)) ^ ((n : ℝ) / 2) * √(2 * (v : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity), add_div]
      have hsqrt : √(2 * π * (v : ℝ)) = √π * √(2 * (v : ℝ)) := by
        rw [← Real.sqrt_mul pi_pos.le, mul_left_comm, mul_assoc]
      rw [Real.inv_rpow (by positivity), hsplit, hsqrt]
      field_simp

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
  have heven_abs : (∫ x, (x - m) ^ (2 * n) ∂gaussianReal m v) =
      ∫ x, |x - m| ^ (2 * n) ∂gaussianReal m v := by
    congr with x
    simp only [pow_mul, sq_abs]
  rw [heven_abs, integral_abs_sub_pow_gaussianReal]
  have hhalf_even : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by norm_num
  have hhalf_succ : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  rw [hhalf_even, Real.rpow_natCast, hhalf_succ, Real.Gamma_nat_add_half]
  field_simp [Real.sqrt_ne_zero'.mpr pi_pos]
  simp only [mul_pow]

/-- The `2n`th centered moment of a real Gaussian distribution is
`vⁿ (2n - 1)‼`. -/
@[simp]
theorem centralMoment_id_two_mul_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (gaussianReal m v) =
      (v : ℝ) ^ n * (2 * n - 1 : ℕ)‼ := by
  simpa only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq, integral_id_gaussianReal]
    using integral_sub_pow_two_mul_gaussianReal m v n

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

/-- Every odd centered moment of a real Gaussian distribution vanishes. -/
@[simp]
theorem centralMoment_id_two_mul_add_one_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n + 1) (gaussianReal m v) = 0 := by
  simpa only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq, integral_id_gaussianReal] using
    IsGaussian.integral_comp_sub_eq_zero_of_odd (gaussianReal m v)
      (f := fun x : ℝ ↦ x ^ (2 * n + 1)) (odd_two_mul_add_one n).neg_pow

end TauCeti.Probability

namespace TauCeti

open MeasureTheory ProbabilityTheory

/-- Exponential moment of a linear form `y ⬝ᵥ g` on a finite product of independent real
Gaussian laws `gaussianReal (μ l) (v l)`: it is integrable, with integral
`exp (r * (y ⬝ᵥ μ) + r ^ 2 / 2 * ∑ l, v l * y l ^ 2)`. -/
theorem integral_exp_mul_dotProduct_pi_gaussianReal {γ : Type*} [Fintype γ]
    (y μ : γ → ℝ) (v : γ → ℝ≥0) (r : ℝ) :
    Integrable (fun g : γ → ℝ ↦ Real.exp (r * (y ⬝ᵥ g)))
        (Measure.pi fun l ↦ gaussianReal (μ l) (v l)) ∧
      ∫ g : γ → ℝ, Real.exp (r * (y ⬝ᵥ g)) ∂(Measure.pi fun l ↦ gaussianReal (μ l) (v l)) =
        Real.exp (r * (y ⬝ᵥ μ) + r ^ 2 / 2 * ∑ l, (v l : ℝ) * y l ^ 2) := by
  simp only [dotProduct]
  -- The linear form is a sum of coordinate statistics, so its mgf factors over the coordinates.
  have hcoord (l : γ) : mgf (fun u : ℝ ↦ y l * u) (gaussianReal (μ l) (v l)) r =
      Real.exp (r * (y l * μ l) + r ^ 2 / 2 * ((v l : ℝ) * y l ^ 2)) := by
    rw [mgf_const_mul, mgf_fun_id_gaussianReal]
    exact congrArg Real.exp (by ring)
  have hmgf : mgf (fun g : γ → ℝ ↦ ∑ l, y l * g l)
      (Measure.pi fun l ↦ gaussianReal (μ l) (v l)) r =
        Real.exp (r * ∑ l, y l * μ l + r ^ 2 / 2 * ∑ l, (v l : ℝ) * y l ^ 2) := by
    rw [TauCeti.mgf_sum_pi (fun l u ↦ y l * u) r]
    simp_rw [hcoord, ← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact ⟨mgf_pos_iff.mp (hmgf ▸ Real.exp_pos _), by simpa only [mgf] using hmgf⟩

end TauCeti
