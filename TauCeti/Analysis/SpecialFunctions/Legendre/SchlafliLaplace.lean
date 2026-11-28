/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.MeasureTheory.Integral.OddSymmetric
import TauCeti.RingTheory.Polynomial.ShiftedLegendre.Rodrigues

/-!
# Schläfli's and Laplace's integrals for the Legendre polynomials

The Legendre polynomial `Pₙ(z)` is Mathlib's shifted Legendre polynomial
`Polynomial.shiftedLegendre n`, mapped to `ℂ` and evaluated at `(1 - z)/2`. Rodrigues' formula
`(d/dz)ⁿ (z² - 1)ⁿ = 2ⁿ n! Pₙ(z)` (`Polynomial.iterate_derivative_X_sq_sub_one_pow`) and Cauchy's
integral formula for derivatives give Schläfli's integral over every circle about `z`. On the
circle of radius `|z² - 1|^{1/2}` it becomes Laplace's integral, which bounds `Pₙ` on `[-1, 1]`.

## Main results

* `Complex.iteratedDeriv_sq_sub_one_pow`: `(d/dz)ⁿ (z² - 1)ⁿ = 2ⁿ n! Pₙ(z)` for every `z : ℂ`.
* `Complex.legP_eq_circleIntegral`: **Schläfli's integral** (DLMF 14.12.8 at `m = 0`),
  `∮_{|t - z| = r} (t² - 1)ⁿ / (2ⁿ (t - z)ⁿ⁺¹) dt = 2πi Pₙ(z)` for `r > 0`.
* `Complex.legP_eq_inv_pi_mul_integral`: **Laplace's integral** (DLMF 14.12.7 at `m = 0`),
  `Pₙ(z) = π⁻¹ ∫₀^π (z + w cos φ)ⁿ dφ` for every `z : ℂ` and either square root `w` of `z² - 1`.
* `Complex.norm_legP_le_one`: `|Pₙ(x)| ≤ 1` for `-1 ≤ x ≤ 1` (Temme (6.52)).

In the theorem names, `legP` stands for `Pₙ(z)`, that is, for the evaluation
`((shiftedLegendre n).map (Int.castRingHom ℂ)).eval ((1 - z) / 2)` displayed in the statements;
it is not a separate definition.

## Attribution

Adapted from lean-DLMF, `DLMF/OrthogonalPolynomials/LegendreComplexLaplace.lean`
(`iteratedDeriv_legendreRodrigues_numerator`, `legendrePolynomialP_eq_circleIntegral`) and
`DLMF/OrthogonalPolynomials/Legendre.lean` (`norm_legendrePolynomialP_le_one`), rewritten for
Mathlib's `Polynomial.shiftedLegendre`. lean-DLMF proves Laplace's integral by the three-term
recurrence; here it follows from Schläfli's integral, as in Whittaker–Watson §15·23.

## References

* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§15·12, 15·23.
* N. M. Temme, *Special Functions*, (6.49), (6.50), (6.52).
* DLMF, *NIST Digital Library of Mathematical Functions*, 14.7.13, 14.12.7, 14.12.8.
-/

public section

open Polynomial MeasureTheory
open scoped Real

namespace Complex

/-- Rodrigues' formula for the Legendre polynomial in the complex variable:
`(d/dz)ⁿ (z² - 1)ⁿ = 2ⁿ n! Pₙ(z)`, with `Pₙ(z)` the shifted Legendre polynomial at `(1 - z)/2`. -/
theorem iteratedDeriv_sq_sub_one_pow (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun t : ℂ => (t ^ 2 - 1) ^ n) z =
      2 ^ n * n.factorial * ((shiftedLegendre n).map (Int.castRingHom ℂ)).eval ((1 - z) / 2) := by
  have h := congrFun (Polynomial.iteratedDeriv ((X ^ 2 - 1 : ℂ[X]) ^ n) n) z
  simp only [eval_pow, eval_sub, eval_X, eval_one] at h
  rw [h, iterate_derivative_X_sq_sub_one_pow]
  simp [div_eq_inv_mul]

/-- **Schläfli's integral** for the Legendre polynomial (DLMF 14.12.8 at `m = 0`): for every
circle about `z`, `∮ (t² - 1)ⁿ / (2ⁿ (t - z)ⁿ⁺¹) dt = 2πi Pₙ(z)`. -/
theorem legP_eq_circleIntegral (n : ℕ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∮ t in C(z, r), (t ^ 2 - 1) ^ n / (2 ^ n * (t - z) ^ (n + 1))) =
      2 * π * I * ((shiftedLegendre n).map (Int.castRingHom ℂ)).eval ((1 - z) / 2) := by
  have hc := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hr n
    (f := fun t : ℂ => (t ^ 2 - 1) ^ n) (c := z) (by fun_prop)
  have he : (fun t : ℂ => (t ^ 2 - 1) ^ n / (2 ^ n * (t - z) ^ (n + 1))) =
      fun t => ((2 : ℂ) ^ n)⁻¹ • ((1 / (t - z) ^ (n + 1)) • (t ^ 2 - 1) ^ n) := by
    funext t
    simp only [smul_eq_mul, div_eq_mul_inv, mul_inv]
    ac_rfl
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [he, circleIntegral.integral_smul, hc, iteratedDeriv_sq_sub_one_pow, smul_eq_mul,
    smul_eq_mul]
  field_simp

/-- On the circle `t = z + w e^{iψ}` the integrand of Schläfli's integral is `i (z + w cos ψ)ⁿ`
times the length element `dψ`, when `w² = z² - 1`. -/
private theorem schlafli_integrand_eq (n : ℕ) {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) (hw₀ : w ≠ 0)
    (ψ : ℝ) :
    (w * exp (ψ * I) * I) * (((z + w * exp (ψ * I)) ^ 2 - 1) ^ n /
      (2 ^ n * (z + w * exp (ψ * I) - z) ^ (n + 1))) = I * (z + w * Real.cos ψ) ^ n := by
  set e := exp (ψ * I) with he_def
  have he : e ≠ 0 := exp_ne_zero _
  have hcos : (Real.cos ψ : ℂ) = (e + e⁻¹) / 2 := by
    rw [ofReal_cos, cos, he_def, ← exp_neg, neg_mul]
  have hkey : (z + w * e) ^ 2 - 1 = 2 * (w * e) * (z + w * Real.cos ψ) := by
    rw [hcos]
    field_simp
    linear_combination -hw
  rw [hkey, add_sub_cancel_left, mul_pow, mul_pow]
  field_simp
  ring

/-- On the circle of radius `|w|` about `z`, with `w² = z² - 1` and `w ≠ 0`, Schläfli's integral is
`2i ∫₀^π (z + w cos φ)ⁿ dφ`. -/
private theorem circleIntegral_schlafli_eq (n : ℕ) {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1)
    (hw₀ : w ≠ 0) :
    (∮ t in C(z, ‖w‖), (t ^ 2 - 1) ^ n / (2 ^ n * (t - z) ^ (n + 1))) =
      2 * I * ∫ φ in (0 : ℝ)..π, (z + w * Real.cos φ) ^ n := by
  set g : ℝ → ℂ := fun ψ => (z + w * Real.cos ψ) ^ n with hg_def
  have hper : Function.Periodic g (2 * π) := fun ψ => by simp only [hg_def, Real.cos_add_two_pi]
  -- the point `z + |w| e^{iθ}` of the circle is `z + w e^{i(θ - arg w)}`
  have hpt (θ : ℝ) : deriv (circleMap z ‖w‖) θ • ((circleMap z ‖w‖ θ ^ 2 - 1) ^ n /
      (2 ^ n * (circleMap z ‖w‖ θ - z) ^ (n + 1))) = I * g (θ - arg w) := by
    have hu : (‖w‖ : ℂ) * exp (θ * I) = w * exp (↑(θ - arg w) * I) := by
      calc (‖w‖ : ℂ) * exp (θ * I) = ‖w‖ * exp (arg w * I) * exp (↑(θ - arg w) * I) := by
            rw [mul_assoc, ← exp_add]
            congr 2
            push_cast
            ring
        _ = _ := by rw [norm_mul_exp_arg_mul_I]
    rw [deriv_circleMap, circleMap_zero, circleMap, hu, smul_eq_mul]
    exact schlafli_integrand_eq n hw hw₀ (θ - arg w)
  have heven : Function.Even g := fun ψ => by simp only [hg_def, Real.cos_neg]
  have h₁ : ∫ x in 0 - arg w..2 * π - arg w, g x = ∫ x in -π..π, g x := by
    convert hper.intervalIntegral_add_eq (0 - arg w) (-π) using 2 <;> ring
  rw [circleIntegral, intervalIntegral.integral_congr (fun θ _ => hpt θ),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right, h₁,
    intervalIntegral.integral_eq_two_smul_of_even heven π, real_smul]
  push_cast
  ring

/-- **Laplace's integral** for the Legendre polynomial (DLMF 14.12.7 at `m = 0`): for every
`z : ℂ` and either square root `w` of `z² - 1`, `Pₙ(z) = π⁻¹ ∫₀^π (z + w cos φ)ⁿ dφ`. -/
theorem legP_eq_inv_pi_mul_integral (n : ℕ) {z w : ℂ} (hw : w ^ 2 = z ^ 2 - 1) :
    ((shiftedLegendre n).map (Int.castRingHom ℂ)).eval ((1 - z) / 2) =
      (π : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..π, (z + w * Real.cos φ) ^ n := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rcases eq_or_ne w 0 with rfl | hw₀
  · have hz : z * z = 1 := by linear_combination -hw
    rcases mul_self_eq_one_iff.mp hz with rfl | rfl <;> simp [hπ]
  · have h := legP_eq_circleIntegral n z (norm_pos_iff.mpr hw₀)
    rw [circleIntegral_schlafli_eq n hw hw₀] at h
    rw [eq_inv_mul_iff_mul_eq₀ hπ]
    refine mul_left_cancel₀ (by simp : (2 * I : ℂ) ≠ 0) ?_
    linear_combination -h

/-- **The bound** `|Pₙ(x)| ≤ 1` for `-1 ≤ x ≤ 1` (Temme (6.52)). -/
theorem norm_legP_le_one (n : ℕ) {x : ℝ} (hx₀ : -1 ≤ x) (hx₁ : x ≤ 1) :
    ‖((shiftedLegendre n).map (Int.castRingHom ℂ)).eval ((1 - (x : ℂ)) / 2)‖ ≤ 1 := by
  set s := Real.sqrt (1 - x ^ 2)
  have hs : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hw : (I * s) ^ 2 = (x : ℂ) ^ 2 - 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hs
    push_cast at this
    linear_combination (-1 : ℂ) * this + (s : ℂ) ^ 2 * I_sq
  have hb : ∀ φ ∈ Set.uIoc 0 π, ‖((x : ℂ) + I * s * Real.cos φ) ^ n‖ ≤ 1 := fun φ _ => by
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    -- the form `a + b * I` with real `a`, `b` that `norm_add_mul_I` takes
    have hab : (x : ℂ) + I * s * Real.cos φ = x + ((s * Real.cos φ : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hab, norm_add_mul_I, Real.sqrt_le_one]
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_sq_le_one φ) (sq_nonneg s)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [legP_eq_inv_pi_mul_integral n hw, norm_mul, norm_inv, norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  calc π⁻¹ * ‖∫ φ in (0 : ℝ)..π, ((x : ℂ) + I * s * Real.cos φ) ^ n‖
      ≤ π⁻¹ * (1 * |π - 0|) := by gcongr
    _ = 1 := by rw [sub_zero, abs_of_pos Real.pi_pos, one_mul, inv_mul_cancel₀ Real.pi_ne_zero]

end Complex
