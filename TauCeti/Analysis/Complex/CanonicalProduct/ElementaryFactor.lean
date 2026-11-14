/-
Copyright (c) 2026 Matteo Cipollina and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Analytic.Order

import Mathlib.Algebra.Ring.GeomSum

/-!
# Weierstrass elementary factors

The primary factor `weierstrassFactor p z` is `(1 - z)` times the exponential of the
first `p` positive logarithmic terms. Its only zero is a simple zero at one, for every genus.
The definition uses Mathlib's `Complex.logTaylor`, with an equivalent finite-sum formula.

Every genus satisfies the sharp bound `‖E_p(z) - 1‖ ≤ ‖z‖ ^ (p + 1)` on the entire closed
unit disk. Radial integration compares its derivative with a nonnegative real profile of
total mass one, including genus zero and the simple zero at one. At genus one the factor is
`(1 - z) * exp z`; its global logarithmic bounds supply the reciprocal Gamma estimates.
The paired rational logarithmic derivative retains this genus-one specialization.

## Provenance

The all-genus elementary-factor definition, normalization and simple-zero formalization are
adapted from Matteo Cipollina's
[PNT+ development](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/fc979d1d71a79bdcd497ee2881413224c59a46b0/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/WeierstrassFactor.lean).
The generic logarithmic-Taylor formulation here also retains the existing native genus-one
estimates and their Mathlib-based proofs.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11 (the genus-one case).
-/

public section

open scoped BigOperators

namespace Complex

/-- The Weierstrass elementary factor of genus `p`. -/
noncomputable def weierstrassFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (-logTaylor (p + 1) (-z))

/-- The primary factor in terms of Mathlib's logarithmic Taylor polynomial. -/
theorem weierstrassFactor_def (p : ℕ) (z : ℂ) :
    weierstrassFactor p z = (1 - z) * exp (-logTaylor (p + 1) (-z)) := by
  rfl

private theorem neg_logTaylor_neg_eq_sum (p : ℕ) (z : ℂ) :
    -logTaylor (p + 1) (-z) = ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1) := by
  have hsign (j : ℕ) : (-1 : ℂ) ^ (j + 1) * (-z) ^ j = -z ^ j := by
    calc
      _ = -((-1 : ℂ) ^ j * (-z) ^ j) := by rw [pow_succ]; ring
      _ = -(((-1 : ℂ) * (-z)) ^ j) := by rw [mul_pow]
      _ = _ := by simp
  simp only [logTaylor, hsign, neg_div, ← Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_range_succ']
  simp

/-- The finite-sum formula for the primary factor, including the empty sum at genus zero. -/
theorem weierstrassFactor_eq_mul_exp_sum (p : ℕ) (z : ℂ) :
    weierstrassFactor p z =
      (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by
  rw [weierstrassFactor_def, neg_logTaylor_neg_eq_sum]

/-- The genus-zero factor is linear. -/
@[simp]
theorem weierstrassFactor_zero_left (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor_eq_mul_exp_sum]

/-- The genus-one factor is `(1 - z) * exp z`. -/
theorem weierstrassFactor_one_left (z : ℂ) :
    weierstrassFactor 1 z = (1 - z) * exp z := by
  simp [weierstrassFactor_eq_mul_exp_sum]

/-- Every elementary factor is normalized to one at the origin. -/
@[simp]
theorem weierstrassFactor_zero (p : ℕ) : weierstrassFactor p 0 = 1 := by
  simp [weierstrassFactor_def, logTaylor_at_zero]

/-- Every elementary factor vanishes at one. -/
@[simp]
theorem weierstrassFactor_one (p : ℕ) : weierstrassFactor p 1 = 0 := by
  simp [weierstrassFactor_def]

/-- The only zero of any elementary factor is one. -/
@[simp]
theorem weierstrassFactor_eq_zero_iff (p : ℕ) {z : ℂ} :
    weierstrassFactor p z = 0 ↔ z = 1 := by
  rw [weierstrassFactor_def, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero]
  exact eq_comm

private theorem hasDerivAt_neg_logTaylor_neg (p : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ -logTaylor (p + 1) (-w))
      (∑ j ∈ Finset.range p, z ^ j) z := by
  have h := ((hasDerivAt_logTaylor p (-z)).comp z (hasDerivAt_neg z)).neg
  simpa only [← mul_pow, neg_one_mul, neg_neg, mul_neg, mul_one, Function.comp_def] using! h

/-- The derivative of a primary factor vanishes to its genus at the origin. -/
theorem hasDerivAt_weierstrassFactor (p : ℕ) (z : ℂ) :
    HasDerivAt (weierstrassFactor p)
      (-z ^ p * exp (-logTaylor (p + 1) (-z))) z := by
  have h := ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).mul
    ((hasDerivAt_neg_logTaylor_neg p z).cexp)
  convert h using 1
  · exact funext (weierstrassFactor_def p)
  · dsimp only [Pi.sub_apply, id_eq]
    have hg := mul_neg_geom_sum z p
    linear_combination -exp (-logTaylor (p + 1) (-z)) * hg

/-- Every primary factor is complex differentiable everywhere. -/
@[fun_prop]
theorem differentiable_weierstrassFactor (p : ℕ) :
    Differentiable ℂ (weierstrassFactor p) :=
  fun z ↦ (hasDerivAt_weierstrassFactor p z).differentiableAt

/-- Every primary factor is analytic at every complex point. -/
@[fun_prop]
theorem analyticAt_weierstrassFactor (p : ℕ) (z : ℂ) :
    AnalyticAt ℂ (weierstrassFactor p) z := by
  rw [show weierstrassFactor p = fun w : ℂ ↦
      (1 - w) * exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1)) from
    funext (weierstrassFactor_eq_mul_exp_sum p)]
  fun_prop

/-- The derivative of a primary factor. -/
@[simp]
theorem deriv_weierstrassFactor (p : ℕ) (z : ℂ) :
    deriv (weierstrassFactor p) z = -z ^ p * exp (-logTaylor (p + 1) (-z)) :=
  (hasDerivAt_weierstrassFactor p z).deriv

/-- The unique zero of every elementary factor is simple. -/
theorem analyticOrderAt_weierstrassFactor_one (p : ℕ) :
    analyticOrderAt (weierstrassFactor p) 1 = 1 := by
  apply (analyticAt_weierstrassFactor p 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (weierstrassFactor_one p)
  simp [deriv_weierstrassFactor]

/-- The rational logarithmic derivative, using total division at the unique zero. -/
theorem logDeriv_weierstrassFactor (p : ℕ) (z : ℂ) :
    logDeriv (weierstrassFactor p) z = -z ^ p / (1 - z) := by
  rw [logDeriv_apply, deriv_weierstrassFactor, weierstrassFactor_def]
  exact mul_div_mul_right _ _ (exp_ne_zero _)

/-- The radial derivative profile has total mass one on the unit interval. -/
private noncomputable abbrev primaryFactorProfile (p : ℕ) (t : ℝ) : ℝ :=
  t ^ p * Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1))

private theorem norm_primaryFactor_derivative_smul_le (p : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖-(t • z) ^ p * exp (-logTaylor (p + 1) (-(t • z)))‖ ≤
      ‖z‖ ^ p * primaryFactorProfile p t := by
  have hs : (-logTaylor (p + 1) (-(t • z))).re ≤
      ∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1) := by
    rw [neg_logTaylor_neg_eq_sum, Complex.re_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    calc
      _ ≤ ‖(t • z) ^ (k + 1) / (k + 1 : ℂ)‖ := re_le_norm _
      _ = (t * ‖z‖) ^ (k + 1) / (k + 1 : ℝ) := by
        rw [norm_div, norm_pow, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
          ← Nat.cast_add_one, norm_natCast, Nat.cast_add_one]
      _ ≤ t ^ (k + 1) / (k + 1) := by
        gcongr
        exact mul_le_of_le_one_right ht hz
  calc
    _ ≤ ‖t • z‖ ^ p * Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1)) := by
      rw [norm_mul, norm_neg, norm_pow, norm_exp]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (by positivity)
    _ = ‖z‖ ^ p * primaryFactorProfile p t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_pow]
      dsimp only [primaryFactorProfile]
      ring

private theorem integral_primaryFactorProfile (p : ℕ) :
    ∫ t : ℝ in 0..1, primaryFactorProfile p t = 1 := by
  have hd (t : ℝ) :
      -((t : ℂ) ^ p) * exp (-logTaylor (p + 1) (-(t : ℂ))) =
        -(primaryFactorProfile p t : ℂ) := by
    rw [neg_logTaylor_neg_eq_sum]
    simp only [primaryFactorProfile, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_exp, Complex.ofReal_sum, Complex.ofReal_div ]
    push_cast
    ring
  let D : ℂ → ℂ := fun w ↦ -w ^ p * exp (-logTaylor (p + 1) (-w))
  have hcont : ContinuousOn (fun t : ℝ ↦ D (0 + t • (1 : ℂ))) (Set.Icc 0 1) := by
    dsimp only [D, logTaylor]
    fun_prop
  have heq : ∫ t : ℝ in 0..1, D (t : ℂ) = -1 := by
    simpa only [zero_add, real_smul, smul_eq_mul, mul_one, one_mul, weierstrassFactor_one,
      weierstrassFactor_zero, zero_sub] using
      (intervalIntegral.integral_unitInterval_deriv_eq_sub hcont
        (fun t _ ↦ hasDerivAt_weierstrassFactor p (0 + t • (1 : ℂ))))
  simp only [D, hd, intervalIntegral.integral_neg, intervalIntegral.integral_ofReal,
    neg_inj] at heq
  exact_mod_cast heq

/-- Every primary factor differs from one by at most its first omitted power on the entire
closed unit disk, including zero genus and the factor's simple zero at one. -/
theorem norm_weierstrassFactor_sub_one_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖weierstrassFactor p z - 1‖ ≤ ‖z‖ ^ (p + 1) := by
  let D : ℂ → ℂ := fun w ↦ -w ^ p * exp (-logTaylor (p + 1) (-w))
  have hcont : ContinuousOn (fun t : ℝ ↦ D (0 + t • z)) (Set.Icc 0 1) := by
    dsimp only [D, logTaylor]
    fun_prop
  have heq : z * ∫ t : ℝ in 0..1, D (t • z) = weierstrassFactor p z - 1 := by
    simpa only [zero_add, smul_eq_mul, weierstrassFactor_zero] using
      (intervalIntegral.integral_unitInterval_deriv_eq_sub hcont
        (fun t _ ↦ hasDerivAt_weierstrassFactor p (0 + t • z)))
  have hbound : ∀ᵐ t : ℝ, t ∈ Set.Ioc 0 1 →
      ‖D (t • z)‖ ≤ ‖z‖ ^ p * primaryFactorProfile p t := by
    filter_upwards with t ht
    exact norm_primaryFactor_derivative_smul_le p ht.1.le hz
  rw [← heq, norm_mul]
  calc
    _ ≤ ‖z‖ * ∫ t : ℝ in 0..1, ‖z‖ ^ p * primaryFactorProfile p t := by
      gcongr
      exact intervalIntegral.norm_integral_le_of_norm_le zero_le_one hbound
        ((continuous_const.mul (by unfold primaryFactorProfile; fun_prop)).intervalIntegrable 0 1)
    _ = ‖z‖ ^ (p + 1) := by
      rw [intervalIntegral.integral_const_mul, integral_primaryFactorProfile, mul_one, pow_succ']

/-- A linear global upper bound for the logarithm of the norm. -/
theorem log_norm_weierstrassFactor_one_le (z : ℂ) :
    Real.log ‖weierstrassFactor 1 z‖ ≤ 2 * ‖z‖ := by
  by_cases hz : z = 1
  · subst z
    simp
  have h : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
  rw [weierstrassFactor_one_left, norm_mul, norm_exp,
    Real.log_mul (ne_of_gt h) (Real.exp_ne_zero _), Real.log_exp]
  have hn : ‖1 - z‖ ≤ 1 + ‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
  have hl := Real.log_le_sub_one_of_pos h
  have hr := re_le_norm z
  linarith

/-- Composing any elementary factor with a nonzero slope preserves its simple root. -/
theorem analyticOrderAt_weierstrassFactor_mul (p : ℕ) {c z : ℂ} (h : c * z = 1) :
    analyticOrderAt (fun w ↦ weierstrassFactor p (c * w)) z = 1 := by
  have hc : c ≠ 0 := by intro hc; simp [hc] at h
  have hd : HasDerivAt (fun w ↦ c * w) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have hg : AnalyticAt ℂ (fun w ↦ c * w) z := by fun_prop
  have heq : (fun w ↦ weierstrassFactor p (c * w)) =
      weierstrassFactor p ∘ (fun w ↦ c * w) := rfl
  rw [heq, analyticOrderAt_comp_of_deriv_ne_zero hg (by rwa [hd.deriv]), h]
  exact analyticOrderAt_weierstrassFactor_one p

/-- The rational logarithmic derivative of the genus-one factor with slope `a`,
using total division at its pole. -/
noncomputable def logDerivWeierstrassFactorOneMul (a z : ℂ) : ℂ :=
  -a ^ 2 * z / (1 - a * z)

/-- The defining rational expression for the slope-dependent logarithmic derivative. -/
theorem logDerivWeierstrassFactorOneMul_def (a z : ℂ) :
    logDerivWeierstrassFactorOneMul a z = -a ^ 2 * z / (1 - a * z) := (rfl)

/-- The slope-dependent logarithmic derivative is quadratic in the slope while `‖a * z‖ ≤ 1 / 2`
keeps its denominator away from zero. -/
theorem norm_logDerivWeierstrassFactorOneMul_le {a z : ℂ} (h : ‖a * z‖ ≤ 1 / 2) :
    ‖logDerivWeierstrassFactorOneMul a z‖ ≤ (2 * ‖z‖) * ‖a‖ ^ 2 := by
  have hden : (1 / 2 : ℝ) ≤ ‖1 - a * z‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (a * z)
    rw [norm_one] at ht
    linarith
  calc
    _ = (‖a‖ ^ 2 * ‖z‖) / ‖1 - a * z‖ := by
      rw [logDerivWeierstrassFactorOneMul_def, norm_div, norm_mul, norm_neg, norm_pow]
    _ ≤ (‖a‖ ^ 2 * ‖z‖) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = (2 * ‖z‖) * ‖a‖ ^ 2 := by ring

/-- At an inverse slope `ρ⁻¹`, the logarithmic derivative is the paired fraction
`1 / (z - ρ) + 1 / ρ` away from the zero `ρ` of the factor. -/
theorem logDerivWeierstrassFactorOneMul_inv {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    logDerivWeierstrassFactorOneMul ρ⁻¹ z = 1 / (z - ρ) + 1 / ρ := by
  have hd : 1 - ρ⁻¹ * z ≠ 0 := sub_ne_zero.mpr fun h ↦
    hz ((inv_mul_eq_one₀ hρ).mp h.symm).symm
  rw [logDerivWeierstrassFactorOneMul_def]
  field_simp [hρ, hd, sub_ne_zero.mpr hz]
  ring

/-- The paired rational logarithmic derivative of an elementary factor with a complex slope. -/
@[simp]
theorem logDeriv_weierstrassFactor_one_mul (a z : ℂ) :
    logDeriv (fun w ↦ weierstrassFactor 1 (a * w)) z = logDerivWeierstrassFactorOneMul a z := by
  rw [logDerivWeierstrassFactorOneMul_def]
  have hd : HasDerivAt (fun w : ℂ ↦ a * w) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  rw [logDeriv_fun_comp (differentiable_weierstrassFactor 1 _) hd.differentiableAt,
    logDeriv_weierstrassFactor 1, hd.deriv]
  ring

/-- The global logarithmic bound in exponential form, which also covers the zero at one. -/
theorem norm_weierstrassFactor_one_le_exp (z : ℂ) :
    ‖weierstrassFactor 1 z‖ ≤ Real.exp (2 * ‖z‖) := by
  rcases (norm_nonneg (weierstrassFactor 1 z)).eq_or_lt with h | h
  · rw [← h]
    positivity
  · rw [← Real.exp_log h]
    exact Real.exp_le_exp.mpr (log_norm_weierstrassFactor_one_le z)

/-- The genus-one factor has a global quadratic exponential bound. -/
theorem norm_weierstrassFactor_one_le_exp_sq (z : ℂ) :
    ‖weierstrassFactor 1 z‖ ≤ Real.exp (3 * ‖z‖ ^ 2) := by
  by_cases hz : ‖z‖ ≤ 1
  · calc
      _ ≤ ‖(1 : ℂ)‖ + ‖weierstrassFactor 1 z - 1‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ 3 * ‖z‖ ^ 2 + 1 := by
        rw [norm_one, add_comm]
        exact add_le_add_left ((norm_weierstrassFactor_sub_one_le 1 hz).trans
          (by norm_num only [Nat.reduceAdd]; nlinarith [sq_nonneg ‖z‖])) 1
      _ ≤ Real.exp (3 * ‖z‖ ^ 2) := Real.add_one_le_exp _
  · exact (norm_weierstrassFactor_one_le_exp z).trans
      (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg z]))

end Complex
