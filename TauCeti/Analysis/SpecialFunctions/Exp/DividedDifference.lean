/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Divided differences of the real and complex exponential

The divided difference of the real exponential is the integral of the exponential along the segment
between its arguments. In particular it is strictly positive, including when the arguments
coincide, and jointly real analytic, including on the diagonal. These divided differences are the
scalar coefficients in the derivative of the matrix exponential at a Hermitian matrix.

For any `[RCLike 𝕜]`,
`dslope NormedSpace.exp a b = NormedSpace.exp a * dslope NormedSpace.exp 0 (b - a)`
(`NormedSpace.dslope_exp_eq_exp_mul_dslope_zero`), specializing to both
`Real.dslope_exp_eq_exp_mul_dslope_zero` and `Complex.dslope_exp_eq_exp_mul_dslope_zero`.
Over `ℂ`, `dslope Complex.exp a b` vanishes if and only if `b - a` is a nonzero integer multiple of
`2 * π * I`. In particular, it does not vanish on the horizontal strip `|(b - a).im| < 2 * π` or on
`Metric.ball a (2 * π)`.
-/

public section

open scoped ContDiff

namespace NormedSpace

/-- Translating the divided difference of `NormedSpace.exp` to zero extracts the factor
`NormedSpace.exp a`. -/
theorem dslope_exp_eq_exp_mul_dslope_zero {𝕜 : Type*} [RCLike 𝕜] (a b : 𝕜) :
    dslope (exp : 𝕜 → 𝕜) a b = exp a * dslope (exp : 𝕜 → 𝕜) 0 (b - a) := by
  by_cases hab : b = a
  · subst hab
    simp [dslope_same, (hasDerivAt_exp (𝕂 := 𝕜) (x := b)).deriv,
      (hasDerivAt_exp (𝕂 := 𝕜) (x := 0)).deriv]
  · have hsub : b - a ≠ 0 := sub_ne_zero.mpr hab
    rw [dslope_of_ne _ hab, dslope_of_ne _ hsub, slope_def_field, slope_def_field]
    simp only [sub_zero, exp_zero]
    rw [← mul_div_assoc, mul_sub, mul_one, ← exp_add, add_sub_cancel]

end NormedSpace

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
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.dslope_exp_eq_exp_mul_dslope_zero a b

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

/-- Factoring out `exp z` rewrites `exp z - 1` as `exp z * (1 - exp (-z))`. -/
theorem exp_sub_one_eq_exp_mul_one_sub_exp_neg (z : ℂ) :
    exp z - 1 = exp z * (1 - exp (-z)) := by
  rw [mul_sub, mul_one, ← exp_add, add_neg_cancel, exp_zero]

/-- Rewriting `exp (-c * z) / (1 - exp (-z))` with denominator `exp z - 1`. -/
theorem exp_neg_mul_div_one_sub_exp_neg (c z : ℂ) :
    exp (-c * z) / (1 - exp (-z)) = exp ((1 - c) * z) / (exp z - 1) := by
  have hnum : exp z * exp (-c * z) = exp ((1 - c) * z) := by
    rw [← exp_add]
    congr 1
    ring
  rw [exp_sub_one_eq_exp_mul_one_sub_exp_neg, ← hnum, mul_div_mul_left _ _ (exp_ne_zero z)]

/-- Translating the complex exponential divided difference to zero extracts the factor `exp a`. -/
theorem dslope_exp_eq_exp_mul_dslope_zero (a b : ℂ) :
    dslope exp a b = exp a * dslope exp 0 (b - a) := by
  simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.dslope_exp_eq_exp_mul_dslope_zero a b

/-- The divided difference `dslope Complex.exp a b` vanishes if and only if `b - a` is a nonzero
integer multiple of `2 * π * I`. -/
theorem dslope_exp_eq_zero_iff {a b : ℂ} :
    dslope exp a b = 0 ↔ ∃ k : ℤ, k ≠ 0 ∧ b - a = k * (2 * Real.pi * I) := by
  rw [dslope_exp_eq_exp_mul_dslope_zero, mul_eq_zero, or_iff_right (exp_ne_zero a)]
  set z := b - a
  have hmul : z * dslope exp 0 z = exp z - 1 := by
    simpa [exp_zero] using sub_smul_dslope exp 0 z
  constructor
  · intro h0
    rcases eq_or_ne z 0 with hz0 | hzne
    · simp [hz0] at h0
    · have hexp : exp z = 1 := by
        have h := hmul
        rw [h0, mul_zero] at h
        exact eq_of_sub_eq_zero h.symm
      obtain ⟨k, hk⟩ := exp_eq_one_iff.mp hexp
      exact ⟨k, fun h => hzne (by simpa [h] using hk), hk⟩
  · rintro ⟨k, hkne, hk⟩
    have hzne : z ≠ 0 := by
      rw [hk]
      exact mul_ne_zero (Int.cast_ne_zero.mpr hkne) (by simp [Real.pi_ne_zero, I_ne_zero])
    have hexp : exp z = 1 := exp_eq_one_iff.mpr ⟨k, hk⟩
    have h := hmul
    rw [hexp, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left hzne

/-- On the horizontal strip `|(b - a).im| < 2 * π`, `dslope Complex.exp a b` does not vanish. -/
theorem dslope_exp_ne_zero_of_abs_im_sub_lt {a b : ℂ} (h : |(b - a).im| < 2 * Real.pi) :
    dslope exp a b ≠ 0 := by
  intro h0
  obtain ⟨k, hkne, hk⟩ := dslope_exp_eq_zero_iff.mp h0
  have him : (b - a).im = k * (2 * Real.pi) := by
    simpa [mul_assoc] using congrArg Complex.im hk
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hkne
  have habs : |(b - a).im| = |(k : ℝ)| * (2 * Real.pi) := by
    rw [him, abs_mul, abs_of_pos Real.two_pi_pos]
  nlinarith [Real.pi_pos]

/-- On the real axis, `dslope Complex.exp (x : ℂ) (y : ℂ)` does not vanish. -/
theorem dslope_exp_ofReal_ne_zero (x y : ℝ) : dslope exp (x : ℂ) (y : ℂ) ≠ 0 :=
  dslope_exp_ne_zero_of_abs_im_sub_lt (by simp [Real.pi_pos])

/-- On `Metric.ball a (2 * π)`, the divided difference `dslope Complex.exp a b` does not vanish. -/
theorem dslope_exp_ne_zero_of_mem_ball {a b : ℂ} (h : b ∈ Metric.ball a (2 * Real.pi)) :
    dslope exp a b ≠ 0 :=
  dslope_exp_ne_zero_of_abs_im_sub_lt <|
    (abs_im_le_norm (b - a)).trans_lt (by simpa [dist_eq_norm] using h)

end Complex
