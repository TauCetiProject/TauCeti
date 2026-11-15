/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Divided differences of the real and complex exponential

The divided difference of the real exponential is the integral of the exponential along the segment
between its arguments. In particular it is strictly positive, including when the arguments
coincide, and jointly real analytic, including on the diagonal. These divided differences are the
scalar coefficients in the derivative of the matrix exponential at a Hermitian matrix.

Over `ℂ`, `dslope Complex.exp a b = Complex.exp a * dslope Complex.exp 0 (b - a)` is entire in `b`
and nonvanishing on `Metric.ball a (2 * π)`, since the nonzero roots of `exp z = 1` lie at distance
at least `2 * π` from the origin.
-/

public section

open scoped ContDiff

namespace Real

/-- The divided difference of the exponential is its average along a segment. -/
theorem dslope_exp_eq_integral (a b : ℝ) :
    dslope exp a b = ∫ t in (0 : ℝ)..1, exp ((1 - t) * a + t * b) := by
  have heq (t : ℝ) : (1 - t) * a + t * b = a + t * (b - a) := by ring
  simp_rw [heq]
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ exp (a + t * (b - a))) (Set.Icc 0 1))
    (fun t _ ↦ hasDerivAt_exp (a + t * (b - a)))
  simp only [smul_eq_mul, add_sub_cancel] at h
  by_cases hab : b = a
  · simp [hab]
  · rw [dslope_of_ne exp hab, slope_def_field, div_eq_iff (sub_ne_zero.mpr hab)]
    simpa only [mul_comm] using h.symm

/-- All divided differences of the real exponential are strictly positive. -/
theorem dslope_exp_pos (a b : ℝ) : 0 < dslope exp a b := by
  rw [dslope_exp_eq_integral]
  exact intervalIntegral.integral_pos (by norm_num) (by fun_prop)
    (fun t _ ↦ (exp_pos _).le) ⟨0, by simp, exp_pos _⟩

/-- Translating the real exponential divided difference to zero extracts the factor `exp a`. -/
theorem dslope_exp_eq_exp_mul_dslope_zero (a b : ℝ) :
    dslope exp a b = exp a * dslope exp 0 (b - a) := by
  rw [dslope_exp_eq_integral a b, dslope_exp_eq_integral 0 (b - a),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← exp_add]
  congr 1
  ring

/-- The real exponential divided difference is jointly smooth, including its removable
value at equal arguments. The regularity parameter also permits real analyticity. -/
theorem contDiff_dslope_exp (m : ℕ∞ω) :
    ContDiff ℝ m (fun p : ℝ × ℝ ↦ dslope exp p.1 p.2) := by
  have hz : ContDiff ℝ m (dslope exp 0) :=
    ((analyticOnNhd_rexp (u := Set.univ)).dslope 0).contDiff
  have h : ContDiff ℝ m (fun p : ℝ × ℝ ↦ exp p.1 * dslope exp 0 (p.2 - p.1)) :=
    (contDiff_fst.exp).mul (hz.comp (contDiff_snd.sub contDiff_fst))
  convert h using 1
  funext p
  exact dslope_exp_eq_exp_mul_dslope_zero p.1 p.2

end Real

namespace Complex

/-- Translating the complex exponential divided difference to zero extracts the factor `exp a`. -/
theorem dslope_exp_eq_exp_mul_dslope_zero (a b : ℂ) :
    dslope exp a b = exp a * dslope exp 0 (b - a) := by
  by_cases hab : b = a
  · simp [hab]
  · have hsub : b - a ≠ 0 := sub_ne_zero.mpr hab
    rw [dslope_of_ne _ hab, dslope_of_ne _ hsub, slope_def_field, slope_def_field]
    simp only [sub_zero, exp_zero]
    rw [← mul_div_assoc, mul_sub, mul_one, ← exp_add, add_sub_cancel]

/-- The divided difference `dslope Complex.exp a` is entire for every basepoint `a : ℂ`. -/
@[fun_prop]
theorem differentiable_dslope_exp (a : ℂ) : Differentiable ℂ (dslope exp a) :=
  differentiableOn_univ.mp ((analyticOnNhd_cexp (u := Set.univ)).dslope a).differentiableOn

/-- On `Metric.ball a (2 * π)`, the divided difference `dslope Complex.exp a b` does not vanish. -/
theorem dslope_exp_ne_zero {a b : ℂ} (h : b ∈ Metric.ball a (2 * Real.pi)) :
    dslope exp a b ≠ 0 := by
  rw [dslope_exp_eq_exp_mul_dslope_zero]
  refine mul_ne_zero (exp_ne_zero a) ?_
  set z := b - a
  rcases eq_or_ne z 0 with hz0 | hzne
  · simp [hz0]
  · intro h0
    have hmul := sub_smul_dslope exp 0 z
    rw [sub_zero, smul_eq_mul, h0, mul_zero, exp_zero, eq_comm, sub_eq_zero] at hmul
    obtain ⟨k, hk⟩ := exp_eq_one_iff.mp hmul
    rcases eq_or_ne k 0 with rfl | hkne
    · simp only [Int.cast_zero, zero_mul] at hk
      exact hzne hk
    · have hk1 : (1 : ℝ) ≤ ‖(k : ℂ)‖ := by
        rw [norm_intCast]; exact_mod_cast Int.one_le_abs hkne
      have hn := congrArg norm hk
      rw [norm_mul, norm_mul, norm_mul, norm_ofNat, norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, norm_I, mul_one] at hn
      have hlt : ‖z‖ < 2 * Real.pi := by simpa [z, dist_eq_norm] using h
      nlinarith [Real.pi_pos]

end Complex
