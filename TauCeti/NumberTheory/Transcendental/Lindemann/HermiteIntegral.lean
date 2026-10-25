/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SumIteratedDerivative
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Hermite's integral

For a complex polynomial `f` and `z : ℂ`, Hermite's integral is
`F_f(z) = z ∫₀¹ exp (z (1 - t)) f(z t) dt`, the integral of `exp (z - u) f(u)` along the segment
from `0` to `z`. Integration by parts evaluates it in terms of the sum of all derivatives
`sumIDeriv f = f + f' + f'' + ⋯`:
`F_f(z) = exp z * (sumIDeriv f)(0) - (sumIDeriv f)(z)` (`Polynomial.hermiteIntegral_eq_sumIDeriv`).

This identity is the analytic input to Hermite's proof of the transcendence of `e` and to the
Hermite–Lindemann proof of the Lindemann–Weierstrass theorem. For a vanishing exponential relation
`∑ δⱼ exp γⱼ = 0` it shows that the polynomial expression `-∑ δⱼ (sumIDeriv f)(γⱼ)` (an algebraic
number when the coefficients of `f`, the weights `δⱼ` and the points `γⱼ` are algebraic) equals the
analytic quantity `∑ δⱼ F_f(γⱼ)` (`Polynomial.sum_mul_hermiteIntegral_of_sum_mul_exp_eq_zero`),
which the elementary estimate `‖F_f(z)‖ ≤ ‖z‖ exp ‖z‖ C` (`Polynomial.norm_hermiteIntegral_le`)
makes small for well-chosen auxiliary polynomials `f`.

## Main declarations

* `Polynomial.hermiteIntegral f z`: Hermite's integral `z ∫₀¹ exp (z (1 - t)) f(z t) dt`.
* `Polynomial.hermiteIntegral_eq_sumIDeriv`: the evaluation by integration by parts.
* `Polynomial.hermiteIntegral_eq_exp_mul_integral`: the equivalent form with kernel `exp (-t z)`.
* `Polynomial.norm_hermiteIntegral_le`: the bound `‖F_f(z)‖ ≤ ‖z‖ exp ‖z‖ C`.
* `Polynomial.sum_mul_hermiteIntegral_of_sum_mul_exp_eq_zero`: the value of `∑ δⱼ F_f(γⱼ)` along
  a vanishing exponential relation.

## Implementation notes

Mathlib's `Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart` (Y. Zhao) proves the same
integration by parts for the kernel `exp (-t z)` in its module-private lemmas
`LindemannWeierstrass.hasDerivAt_cexp_mul_sumIDeriv` and
`LindemannWeierstrass.integral_exp_mul_eval`; the derivative computation here follows them.
Since they are not exported, this file states Hermite's integral and its estimates as public API.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 4, §4.1, Lemma 4.2, Corollary 4.3 and
  Lemma 4.4, and §4.2, Lemma 4.12.
-/

public section

open Complex intervalIntegral

namespace Polynomial

/-- Hermite's integral `F_f(z) = z ∫₀¹ exp ((1 - t) z) f(t z) dt` of a complex polynomial `f`,
the integral of `exp (z - u) f(u)` along the segment from `0` to `z`. -/
noncomputable def hermiteIntegral (f : ℂ[X]) (z : ℂ) : ℂ :=
  z * ∫ t in (0 : ℝ)..1, cexp ((1 - t) • z) * f.eval (t • z)

/-- The integrand of Hermite's integral, multiplied by `z`, is the derivative of
`t ↦ -exp ((1 - t) z) (sumIDeriv f)(t z)`. -/
private theorem hasDerivAt_neg_cexp_mul_eval_sumIDeriv (f : ℂ[X]) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ -(cexp ((1 - t) • z) * (sumIDeriv f).eval (t • z)))
      (z * (cexp ((1 - t) • z) * f.eval (t • z))) t := by
  have hlin : HasDerivAt (fun t : ℝ ↦ t • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  have hexp : HasDerivAt (fun t : ℝ ↦ cexp ((1 - t) • z)) (cexp ((1 - t) • z) * -z) t := by
    have h : HasDerivAt (fun t : ℝ ↦ (1 - t) • z) (-z) t := by
      simpa using ((hasDerivAt_id t).const_sub 1).smul_const z
    exact h.cexp
  refine ((hexp.mul (((sumIDeriv f).hasDerivAt (t • z)).comp t hlin)).neg).congr_deriv ?_
  have hS : (sumIDeriv f).eval (t • z) =
      f.eval (t • z) + (derivative (sumIDeriv f)).eval (t • z) := by
    conv_lhs => rw [sumIDeriv_eq_self_add f, eval_add]
  rw [Function.comp_apply, hS]
  ring

/-- **Hermite's identity**: integration by parts evaluates Hermite's integral as
`F_f(z) = exp z * (sumIDeriv f)(0) - (sumIDeriv f)(z)`. -/
theorem hermiteIntegral_eq_sumIDeriv (f : ℂ[X]) (z : ℂ) :
    hermiteIntegral f z = cexp z * (sumIDeriv f).eval 0 - (sumIDeriv f).eval z := by
  rw [hermiteIntegral, ← integral_const_mul,
    integral_eq_sub_of_hasDerivAt (fun t _ ↦ hasDerivAt_neg_cexp_mul_eval_sumIDeriv f z t)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp only [sub_self, zero_smul, one_smul, sub_zero, Complex.exp_zero, one_mul]
  ring

/-- Hermite's integral with the kernel `exp (-t z)`:
`F_f(z) = exp z * (z ∫₀¹ exp (-t z) f(t z) dt)`. -/
theorem hermiteIntegral_eq_exp_mul_integral (f : ℂ[X]) (z : ℂ) :
    hermiteIntegral f z = cexp z * (z * ∫ t in (0 : ℝ)..1, cexp (-(t • z)) * f.eval (t • z)) := by
  rw [hermiteIntegral, mul_left_comm (cexp z), ← integral_const_mul (cexp z)]
  refine congrArg (z * ·) (integral_congr fun t _ ↦ ?_)
  rw [← mul_assoc, ← Complex.exp_add, sub_smul, one_smul, sub_eq_add_neg]

/-- **Hermite's estimate**: if `C` bounds `‖f‖` on the closed disc of radius `‖z‖`, then
`‖F_f(z)‖ ≤ ‖z‖ exp ‖z‖ C`. -/
theorem norm_hermiteIntegral_le {f : ℂ[X]} {z : ℂ} {C : ℝ}
    (hC : ∀ u : ℂ, ‖u‖ ≤ ‖z‖ → ‖f.eval u‖ ≤ C) :
    ‖hermiteIntegral f z‖ ≤ ‖z‖ * Real.exp ‖z‖ * C := by
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp))
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖cexp ((1 - t) • z) * f.eval (t • z)‖ ≤ Real.exp ‖z‖ * C := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht₀ : 0 ≤ 1 - t := sub_nonneg.2 ht.2
    rw [norm_mul, norm_exp]
    refine mul_le_mul ?_ (hC _ ?_) (norm_nonneg _) (Real.exp_pos _).le
    · refine Real.exp_le_exp.2 ((re_le_norm _).trans ?_)
      rw [norm_smul, Real.norm_of_nonneg ht₀]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
    · rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hint := norm_integral_le_of_norm_le_const hpt
  rw [sub_zero, abs_one, mul_one] at hint
  rw [hermiteIntegral, norm_mul, mul_assoc]
  gcongr

/-- Hermite's integral vanishes at `z = 0`. -/
@[simp]
theorem hermiteIntegral_zero_right (f : ℂ[X]) : hermiteIntegral f 0 = 0 := by
  simp [hermiteIntegral]

/-- Hermite's integral of the zero polynomial vanishes. -/
@[simp]
theorem hermiteIntegral_zero_left (z : ℂ) : hermiteIntegral 0 z = 0 := by
  simp [hermiteIntegral_eq_sumIDeriv]

/-- Hermite's integral is additive in the polynomial. -/
@[simp]
theorem hermiteIntegral_add (f g : ℂ[X]) (z : ℂ) :
    hermiteIntegral (f + g) z = hermiteIntegral f z + hermiteIntegral g z := by
  simp only [hermiteIntegral_eq_sumIDeriv, map_add, eval_add]
  ring

/-- Hermite's integral is homogeneous in the polynomial. -/
@[simp]
theorem hermiteIntegral_smul (c : ℂ) (f : ℂ[X]) (z : ℂ) :
    hermiteIntegral (c • f) z = c • hermiteIntegral f z := by
  simp only [hermiteIntegral_eq_sumIDeriv, map_smul, eval_smul, smul_eq_mul]
  ring

/-- Hermite's integral of `C c * f` is `c` times that of `f`. -/
@[simp]
theorem hermiteIntegral_C_mul (c : ℂ) (f : ℂ[X]) (z : ℂ) :
    hermiteIntegral (C c * f) z = c * hermiteIntegral f z := by
  rw [← smul_eq_C_mul, hermiteIntegral_smul, smul_eq_mul]

/-- Hermite's integral commutes with negation of the polynomial. -/
@[simp]
theorem hermiteIntegral_neg (f : ℂ[X]) (z : ℂ) :
    hermiteIntegral (-f) z = -hermiteIntegral f z := by
  simpa using hermiteIntegral_smul (-1) f z

/-- Hermite's integral commutes with subtraction of polynomials. -/
@[simp]
theorem hermiteIntegral_sub (f g : ℂ[X]) (z : ℂ) :
    hermiteIntegral (f - g) z = hermiteIntegral f z - hermiteIntegral g z := by
  rw [sub_eq_add_neg, hermiteIntegral_add, hermiteIntegral_neg, sub_eq_add_neg]

/-- Hermite's integral commutes with finite sums of polynomials. -/
@[simp]
theorem hermiteIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (z : ℂ) :
    hermiteIntegral (∑ i ∈ s, f i) z = ∑ i ∈ s, hermiteIntegral (f i) z := by
  simp only [hermiteIntegral_eq_sumIDeriv, map_sum, eval_finsetSum, Finset.mul_sum,
    Finset.sum_sub_distrib]

/-- Hermite's integral of a constant `c` is `c (exp z - 1)`. -/
@[simp]
theorem hermiteIntegral_C (c : ℂ) (z : ℂ) : hermiteIntegral (C c) z = c * (cexp z - 1) := by
  rw [hermiteIntegral_eq_sumIDeriv, sumIDeriv_C, eval_C, eval_C]
  ring

/-- Hermite's integral of the constant polynomial `1` is `exp z - 1`. -/
@[simp]
theorem hermiteIntegral_one (z : ℂ) : hermiteIntegral 1 z = cexp z - 1 := by
  simpa using hermiteIntegral_C 1 z

/-- Hermite's integral of `X` is `exp z - z - 1`. -/
@[simp]
theorem hermiteIntegral_X (z : ℂ) : hermiteIntegral X z = cexp z - z - 1 := by
  -- `Polynomial.sumIDeriv_X` is stated over `ℕ` only, so unfold one step of `sumIDeriv` instead.
  rw [hermiteIntegral_eq_sumIDeriv, sumIDeriv_eq_self_add, ← sumIDeriv_derivative, derivative_X,
    ← C_1, sumIDeriv_C]
  simp only [eval_add, eval_X, eval_C]
  ring

/-- **Hermite's integral along an exponential relation**: if `∑ δⱼ exp γⱼ = 0`, then
`∑ δⱼ F_f(γⱼ) = -∑ δⱼ (sumIDeriv f)(γⱼ)`, so that the right-hand side (algebraic when the
coefficients of `f`, the weights `δⱼ` and the points `γⱼ` are algebraic) is controlled by the
analytic left-hand side. -/
theorem sum_mul_hermiteIntegral_of_sum_mul_exp_eq_zero {ι : Type*} (s : Finset ι)
    (δ γ : ι → ℂ) (h : ∑ j ∈ s, δ j * cexp (γ j) = 0) (f : ℂ[X]) :
    ∑ j ∈ s, δ j * hermiteIntegral f (γ j) = -∑ j ∈ s, δ j * (sumIDeriv f).eval (γ j) := by
  simp only [hermiteIntegral_eq_sumIDeriv, mul_sub, Finset.sum_sub_distrib, ← mul_assoc,
    ← Finset.sum_mul, h, zero_mul, zero_sub]

end Polynomial
