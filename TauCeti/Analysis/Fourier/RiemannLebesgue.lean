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

The same factor has modulus `1` and is continuous in `t`, so it multiplies an integrable function
into an integrable one, also after multiplying by a bounded continuous function such as the
simple-pole factor `1 / (σ + i t - 1)` for `σ > 1`.

## Main declarations

* `TauCeti.continuous_cpow_mul_I`, `TauCeti.norm_cpow_mul_I`: the factor `x ^ (t * I)` is
  continuous in `t` and has modulus `1`.
* `TauCeti.integrable_inv_sub_one_mul_mul_cpow`: the simple-pole integrand
  `1 / (σ + t I - 1) * psi t * x ^ (t I)` is integrable when `psi` is.

* `TauCeti.tendsto_integral_cpow_mul_I_smul_atTop`: the integral `∫ t, x ^ (t * I) • f t` tends
  to `0` as `x → ∞`, for an arbitrary `f` valued in a complex normed space.
-/

public section

open Complex Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Riemann--Lebesgue on a vertical line**: the integral of `f` against the oscillating factor
`x ^ (i t)` tends to `0` as `x → ∞`.

No hypothesis is needed on `f`. A limit along `atTop` only sees `x > 0`, and there the factor
`x ^ (i t)` has modulus `1`, so the integrand is integrable exactly when `f` is; when `f` is not
integrable both the left-hand side and the limit are `0`. (For `x ≤ 0` the equivalence fails —
at `x = 0` the integrand vanishes almost everywhere, and for `x < 0` the branch of the complex
power contributes a factor of modulus `exp (-π t)` — but those scales are irrelevant here.) -/
theorem tendsto_integral_cpow_mul_I_smul_atTop (f : ℝ → E) :
    Tendsto (fun x : ℝ ↦ ∫ t : ℝ, (x : ℂ) ^ (t * I) • f t) atTop (𝓝 0) := by
  have hfreq : Tendsto (fun x : ℝ ↦ -(Real.log x / (2 * π))) atTop (cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp
      (Real.tendsto_log_atTop.atTop_div_const (by positivity))).mono_right atBot_le_cocompact
  refine ((Real.tendsto_integral_exp_smul_cocompact f).comp hfreq).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rw [Circle.smul_def, Real.fourierChar_apply, cpow_def_of_ne_zero (mod_cast hx.ne'),
    ← ofReal_log hx.le]
  congr 2
  simp [field]

/-- The oscillating factor `t ↦ x ^ (t * I)` is continuous for `x > 0`. -/
theorem continuous_cpow_mul_I {x : ℝ} (hx : 0 < x) : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
  continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])

/-- The oscillating factor `x ^ (t * I)` has modulus `1` for `x > 0`. -/
@[simp]
theorem norm_cpow_mul_I {x : ℝ} (hx : 0 < x) (t : ℝ) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- The simple-pole integrand `1 / (s - 1) * psi * x ^ (i t)` on the line `Re s = sigma > 1` is
integrable once `psi` is: the pole factor is bounded by `(sigma - 1)⁻¹`. -/
theorem integrable_inv_sub_one_mul_mul_cpow {psi : ℝ → ℂ} {x sigma : ℝ} (hpsi : Integrable psi)
    (hx : 0 < x) (hsigma : 1 < sigma) :
    Integrable fun t : ℝ ↦ (1 / (sigma + t * I - 1)) * psi t * x ^ (t * I) := by
  have hdenom (t : ℝ) : (sigma : ℂ) + t * I - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hpolebound (t : ℝ) :
      ‖1 / ((sigma : ℂ) + t * I - 1) * (x : ℂ) ^ (t * I)‖ ≤ (sigma - 1)⁻¹ := by
    rw [norm_mul, norm_cpow_mul_I hx, mul_one, norm_div, norm_one, one_div]
    refine inv_anti₀ (by linarith) ?_
    calc
      sigma - 1 = ((sigma : ℂ) + t * I - 1).re := by simp
      _ ≤ _ := re_le_norm _
  exact (hpsi.bdd_mul (f := fun t : ℝ ↦ 1 / ((sigma : ℂ) + t * I - 1) * (x : ℂ) ^ (t * I))
    ((continuous_const.div (by fun_prop) hdenom).mul
      (continuous_cpow_mul_I hx)).aestronglyMeasurable (.of_forall hpolebound)).congr
    (.of_forall fun t ↦ by ring)

end TauCeti
