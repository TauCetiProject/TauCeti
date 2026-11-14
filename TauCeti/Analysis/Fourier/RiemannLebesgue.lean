/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Riemann--Lebesgue for Fourier coefficients and along a vertical line

The Fourier coefficients of any function on the circle `AddCircle T` tend to `0` as the frequency
`n → ±∞`, that is, along the cofinite filter on `ℤ`. This is Mathlib's Riemann--Lebesgue lemma on
`ℝ` applied to the restriction of the function to a period interval. As there, no hypothesis on
the function is needed: if it is not integrable, every coefficient is `0`. The same holds for the
coefficients `fourierCoeffOn` of a function on an interval `[a, b]`.

Testing a function on the vertical line `Re s = c` against a Dirichlet series produces the
oscillating factor `x ^ (i t)`, which is the Fourier character of frequency `-(2π)⁻¹ log x` in
the variable `t`. Letting `x → ∞` therefore pushes the frequency out of every compact set, and the
Riemann--Lebesgue lemma makes the integral vanish.

The same factor has modulus `1` and is continuous in `t`, so it multiplies an integrable function
into an integrable one, also after multiplying by a bounded continuous function such as the
simple-pole factor `1 / (σ + i t - 1)` for `σ > 1`.

## Main declarations

* `TauCeti.tendsto_fourierCoeff_cofinite`, `TauCeti.tendsto_fourierCoeffOn_cofinite`: the Fourier
  coefficients of any function on the circle, or on an interval, tend to `0` as `n → ±∞`.
* `TauCeti.continuous_cpow_mul_I`, `TauCeti.norm_cpow_mul_I`: the factor `x ^ (t * I)` is
  continuous in `t` and has modulus `1`.
* `TauCeti.integrable_inv_sub_one_mul_mul_cpow`: the simple-pole integrand
  `1 / (σ + t I - 1) * psi t * x ^ (t I)` is integrable when `psi` is.

* `TauCeti.tendsto_integral_cpow_mul_I_smul_atTop`: the integral `∫ t, x ^ (t * I) • f t` tends
  to `0` as `x → ∞`, for an arbitrary `f` valued in a complex normed space.
-/

public section

open Complex Filter MeasureTheory Set
open scoped FourierTransform Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Riemann--Lebesgue for Fourier coefficients**: the Fourier coefficients of any function on
`AddCircle T` tend to `0` as `n → ±∞`. If `f` is not integrable, every coefficient is `0`. -/
theorem tendsto_fourierCoeff_cofinite {T : ℝ} [hT : Fact (0 < T)] (f : AddCircle T → E) :
    Tendsto (fourierCoeff f) cofinite (𝓝 0) := by
  have hfreq : Tendsto (fun n : ℤ ↦ (n : ℝ) * T⁻¹) cofinite (cocompact ℝ) :=
    ((Homeomorph.mulRight₀ T⁻¹ (inv_ne_zero hT.out.ne')).isClosedEmbedding.tendsto_cocompact).comp
      Int.tendsto_coe_cofinite
  have h := ((Real.tendsto_integral_exp_smul_cocompact
    ((Ioc 0 T).indicator fun x : ℝ ↦ f x)).comp hfreq).const_smul (1 / T)
  rw [smul_zero] at h
  refine h.congr fun n ↦ ?_
  rw [fourierCoeff_eq_intervalIntegral f n 0, zero_add, intervalIntegral.integral_of_le hT.out.le,
    ← integral_indicator measurableSet_Ioc]
  congr 1
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [indicator_apply]
  split_ifs
  · rw [Circle.smul_def, Real.fourierChar_apply, fourier_coe_apply]
    congr 2
    push_cast
    field_simp
  · simp

/-- **Riemann--Lebesgue for Fourier coefficients on an interval**: the Fourier coefficients
`fourierCoeffOn hab f n` of any function `f` on `[a, b]` tend to `0` as `n → ±∞`. -/
theorem tendsto_fourierCoeffOn_cofinite {a b : ℝ} (hab : a < b) (f : ℝ → E) :
    Tendsto (fourierCoeffOn hab f) cofinite (𝓝 0) := by
  -- `fourierCoeffOn` is defined as the Fourier coefficient of the `(b - a)`-periodic lift of `f`.
  have := Fact.mk (sub_pos.2 hab)
  exact tendsto_fourierCoeff_cofinite _

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
