/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Cycle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Probability.Distributions.CircularLaw

/-!
# Disk monomial moments via complex circle Stokes and the circular law

This example file cross-checks the complex circle Stokes formula
`TauCeti.integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv`
against the circular-law disk-moment formula
`TauCeti.Probability.integral_pow_mul_conj_pow_circularLaw` by evaluating
`∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n`
(`TauCeti.Examples.Pompeiu.integral_unitBall_pow_mul_conj_pow`)
via `∂ (((m + 1)⁻¹) * z ^ (m + 1) * conj z ^ n)` and the unit-circle residue integral.
-/

public noncomputable section

open Complex ComplexConjugate MeasureTheory Metric Set
open scoped Real

namespace TauCeti.Examples.Pompeiu

private theorem wirtingerDeriv_monomial_div (m n : ℕ) (z : ℂ) :
    wirtingerDeriv (fun w : ℂ ↦ ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * conj w ^ n)) z 1 =
      z ^ m * conj z ^ n := by
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hconst : (fun w : ℂ ↦ ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * conj w ^ n)) =
      ((m : ℂ) + 1)⁻¹ • fun w : ℂ ↦ (w ^ (m + 1)) • conj (w ^ n) := by
    ext w; simp [smul_eq_mul]
  have hg : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ (m + 1)) z :=
    (hasDerivAt_pow (m + 1) z).differentiableAt
  have hgn : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z := (hasDerivAt_pow n z).differentiableAt
  have hh : DifferentiableAt ℝ (fun w : ℂ ↦ conj (w ^ n)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (hgn.restrictScalars ℝ)
  rw [hconst, wirtingerDeriv_const_smul, smul_apply,
    wirtingerDeriv_smul_apply (hg.restrictScalars ℝ) hh 1,
    hgn.wirtingerDeriv_conj_comp_eq_zero, hg.wirtingerDeriv_eq_fderiv,
    (hasDerivAt_pow (m + 1) z).hasFDerivAt.fderiv]
  simp only [zero_apply, smul_eq_mul, mul_zero, zero_add, ContinuousLinearMap.toSpanSingleton_apply,
    one_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_pow]
  field_simp [hm1]

private theorem integral_unitCircle_monomial_conj_deriv (m n : ℕ) :
    (∫ θ in 0..2 * π,
        (((m : ℂ) + 1)⁻¹ * (circleMap 0 1 θ ^ (m + 1) * conj (circleMap 0 1 θ) ^ n)) *
          conj (deriv (circleMap 0 1) θ)) =
      -((m : ℂ) + 1)⁻¹ * ∮ z in C(0, 1), (z - 0) ^ ((m : ℤ) - n - 1) := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  set w : ℂ := circleMap 0 1 θ
  have hw_norm : ‖w‖ = 1 := by simp [w]
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw_norm
  have hpow : w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I) = -(w * I * w ^ ((m : ℤ) - n - 1)) := by
    rw [zpow_sub₀ hw0, zpow_sub₀ hw0, zpow_one, zpow_natCast, zpow_natCast, inv_pow]
    field_simp [hw0]
    ring
  have hdw : deriv (circleMap 0 1) θ = w * I := by simp [deriv_circleMap, w]
  simp only [hdw, map_mul, conj_I, (Complex.inv_eq_conj hw_norm).symm, sub_zero, smul_eq_mul]
  calc
    ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * w⁻¹ ^ n) * (w⁻¹ * -I)
        = ((m : ℂ) + 1)⁻¹ * (w ^ (m + 1) * w⁻¹ ^ n * (w⁻¹ * -I)) := by ring
    _ = -((m : ℂ) + 1)⁻¹ * (w * I * w ^ ((m : ℤ) - n - 1)) := by rw [hpow]; ring

/-- Evaluate the unit-disk monomial moment `∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n` by the
complex circle Stokes formula. -/
theorem integral_unitBall_pow_mul_conj_pow (m n : ℕ) :
    (∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n) =
      if m = n then (Real.pi : ℂ) / ((m : ℂ) + 1) else 0 := by
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  let F : ℂ → ℂ := fun z ↦ ((m : ℂ) + 1)⁻¹ * (z ^ (m + 1) * conj z ^ n)
  have hF : ContDiff ℝ 1 F :=
    contDiff_const.mul ((contDiff_id.pow (m + 1)).mul (Complex.conjCLE.contDiff.pow n))
  have hstokes :=
    integral_mul_conj_deriv_circleMap_eq_neg_two_mul_I_mul_integral_ball_wirtingerDeriv (c := 0)
      (R := 1) isOpen_univ (subset_univ _) hF.contDiffOn
  rw [abs_one] at hstokes
  simp_rw [F, wirtingerDeriv_monomial_div, integral_unitCircle_monomial_conj_deriv] at hstokes
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num) I_ne_zero : (-2 * I : ℂ) ≠ 0)
  rw [← hstokes]
  split_ifs with hmn
  · subst hmn
    rw [sub_self, zero_sub]
    simp_rw [zpow_neg_one]
    rw [circleIntegral.integral_sub_center_inv 0 one_ne_zero]
    field_simp [hm1]
  · rw [circleIntegral.integral_sub_zpow_of_ne (by omega : ((m : ℤ) - n - 1) ≠ -1),
      mul_zero, mul_zero]

-- Cross-check: the circle Stokes evaluation of `∫ z in ball 0 1, z ^ m * conj z ^ n` agrees
-- with `TauCeti.Probability.integral_pow_mul_conj_pow_circularLaw`.
example (m n : ℕ) :
    (∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n) =
      (Real.pi : ℂ) * (if m = n then ((1 / (m + 1) : ℝ) : ℂ) else 0) := by
  rw [← TauCeti.Probability.integral_pow_mul_conj_pow_circularLaw,
    TauCeti.Probability.circularLaw_eq_smul_restrict, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.pi_pos.le), Complex.real_smul,
    Complex.ofReal_inv, integral_unitBall_pow_mul_conj_pow]
  split_ifs <;> simp [Real.pi_ne_zero]

end TauCeti.Examples.Pompeiu

end
