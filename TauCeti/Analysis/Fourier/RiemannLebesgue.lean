/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Riemann--Lebesgue along a vertical line

Testing a function on the vertical line `Re s = c` against a Dirichlet series produces the
oscillating factor `x ^ (i t)`, which is the Fourier character of frequency `-(2π)⁻¹ log x` in
the variable `t`. Letting `x → ∞` therefore pushes the frequency out of every compact set, and the
Riemann--Lebesgue lemma makes the integral vanish.

## Main declarations

* `TauCeti.tendsto_integral_mul_cpow_mul_I_atTop`: the integral `∫ t, f t * x ^ (t * I)` tends to
  `0` as `x → ∞`, for an arbitrary `f : ℝ → ℂ`.
-/

public section

open Complex Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace TauCeti

/-- **Riemann--Lebesgue on a vertical line**: the integral of `f` against the oscillating factor
`x ^ (i t)` tends to `0` as `x → ∞`.

No hypothesis is needed on `f`. The integrand is integrable exactly when `f` is, so when `f` is
not integrable both the left-hand side and the limit are `0`. -/
theorem tendsto_integral_mul_cpow_mul_I_atTop (f : ℝ → ℂ) :
    Tendsto (fun x : ℝ ↦ ∫ t : ℝ, f t * (x : ℂ) ^ (t * I)) atTop (𝓝 0) := by
  have hfreq : Tendsto (fun x : ℝ ↦ -(Real.log x / (2 * π))) atTop (cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp
      (Real.tendsto_log_atTop.atTop_div_const (by positivity))).mono_right atBot_le_cocompact
  refine Tendsto.congr' ?_ ((Real.tendsto_integral_exp_smul_cocompact f).comp hfreq)
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  change (∫ t : ℝ, 𝐞 (-(t * -(Real.log x / (2 * π)))) • f t) = ∫ t : ℝ, f t * (x : ℂ) ^ (t * I)
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le, mul_comm]
  congr 2
  push_cast
  field_simp

end TauCeti
