/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Explicit digamma bounds on the positive real axis

For `x > 0`, the digamma function is real and satisfies
`log x - 1 / x ≤ ψ(x) ≤ log x`. Consequently its difference from the
principal complex logarithm has norm at most `1 / x` on the whole positive
real axis. The real restriction is also monotone.

The proof uses Mathlib's convexity theorem `Real.convexOn_log_Gamma` and
its secant-slope bounds. The gamma recurrence identifies the unit-step
secant slope with `log x`, and the digamma recurrence gives the lower
bound. `HasDerivAt.comp_ofReal` and `HasDerivAt.ofReal_comp` identify the
complex digamma value with the logarithmic derivative of `Real.Gamma` at
regular real points.
-/

public section

open Complex Filter Set Topology

namespace Complex

private theorem real_ne_neg_nat_of_pos {x : ℝ} (hx : 0 < x) :
    ∀ m : ℕ, x ≠ -(m : ℝ) := by
  intro m
  have hm := Nat.cast_nonneg (α := ℝ) m
  linarith

private theorem deriv_Gamma_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    deriv Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hpoles : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    exact hx m (by exact_mod_cast hm)
  have hc := (differentiableAt_Gamma _ hpoles).hasDerivAt.comp_ofReal
  have hr := (Real.differentiableAt_Gamma hx).hasDerivAt.ofReal_comp
  have heq : (fun y : ℝ ↦ Gamma (y : ℂ)) = fun y ↦ (Real.Gamma y : ℂ) :=
    funext Gamma_ofReal
  rw [heq] at hc
  exact hc.unique hr

/-- At a regular real point, the complex digamma value is the real gamma function's
logarithmic derivative. -/
theorem digamma_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma (x : ℂ) = ((logDeriv Real.Gamma x : ℝ) : ℂ) := by
  rw [digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx, Gamma_ofReal, logDeriv_apply,
    ofReal_div]

end Complex

namespace Real

/-- On the positive real axis, the derivative of the real logarithm of gamma
is the real part of the digamma function. -/
theorem hasDerivAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (log ∘ Gamma) (Complex.digamma (x : ℂ)).re x := by
  have hd := (hasDerivAt_Gamma_of_pos hx).differentiableAt.hasDerivAt.log
    (Gamma_pos_of_pos hx).ne'
  simpa only [Function.comp_def, Complex.digamma_ofReal (Complex.real_ne_neg_nat_of_pos hx),
    Complex.ofReal_re, logDeriv_apply] using hd

end Real

namespace Complex

private theorem log_Gamma_slope {x : ℝ} (hx : 0 < x) :
    slope (Real.log ∘ Real.Gamma) x (x + 1) = Real.log x := by
  rw [slope_def_field, Function.comp_apply, Function.comp_apply,
    show x + 1 - x = 1 by ring, div_one,
    Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

/-- The digamma function is bounded above by the logarithm on the positive real axis. -/
theorem re_digamma_le_log {x : ℝ} (hx : 0 < x) :
    (digamma (x : ℂ)).re ≤ Real.log x := by
  have h := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt hx
    (by change 0 < x + 1; linarith) (by linarith) (Real.hasDerivAt_log_Gamma hx)
  rwa [log_Gamma_slope hx] at h

/-- On the positive real axis, the digamma function is bounded below by
`log x - 1 / x`. -/
theorem log_sub_inv_le_re_digamma {x : ℝ} (hx : 0 < x) :
    Real.log x - x⁻¹ ≤ (digamma (x : ℂ)).re := by
  have h := Real.convexOn_log_Gamma.slope_le_of_hasDerivAt hx
    (by change 0 < x + 1; linarith) (by linarith)
    (Real.hasDerivAt_log_Gamma (by linarith : 0 < x + 1))
  rw [log_Gamma_slope hx] at h
  have hpoles : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    exact real_ne_neg_nat_of_pos hx m (by exact_mod_cast hm)
  have hrec := congrArg Complex.re (digamma_apply_add_one (x : ℂ) hpoles)
  simp only [add_re, ← ofReal_inv, ofReal_re] at hrec
  rw [ofReal_add, ofReal_one, hrec] at h
  linarith

/-- An explicit error bound for the digamma asymptotic, valid on the whole positive real axis. -/
theorem norm_digamma_ofReal_sub_log_le {x : ℝ} (hx : 0 < x) :
    ‖digamma (x : ℂ) - log (x : ℂ)‖ ≤ x⁻¹ := by
  rw [digamma_ofReal (real_ne_neg_nat_of_pos hx), ← ofReal_log hx.le, ← ofReal_sub, norm_real,
    Real.norm_eq_abs, abs_le]
  have hu := re_digamma_le_log hx
  have hl := log_sub_inv_le_re_digamma hx
  rw [digamma_ofReal (real_ne_neg_nat_of_pos hx), ofReal_re] at hu hl
  constructor <;> linarith

/-- The real restriction of the digamma function is monotone on the positive real axis. -/
theorem monotoneOn_re_digamma :
    MonotoneOn (fun x : ℝ ↦ (digamma (x : ℂ)).re) (Ioi 0) := by
  have hm := Real.convexOn_log_Gamma.monotoneOn_deriv
    (fun x hx ↦ (Real.hasDerivAt_log_Gamma hx).differentiableAt)
  intro x hx y hy hxy
  simpa only [(Real.hasDerivAt_log_Gamma hx).deriv, (Real.hasDerivAt_log_Gamma hy).deriv] using
    hm hx hy hxy

/-- The digamma function differs from the principal logarithm by `O(1 / x)`
as positive real `x` tends to infinity. -/
theorem isBigO_digamma_ofReal_sub_log :
    (fun x : ℝ ↦ digamma (x : ℂ) - log (x : ℂ)) =O[atTop] (fun x : ℝ ↦ x⁻¹) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)] using
    norm_digamma_ofReal_sub_log_le hx

end Complex
