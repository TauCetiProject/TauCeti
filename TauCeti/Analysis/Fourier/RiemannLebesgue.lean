/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Riemann--Lebesgue for Fourier coefficients, sine modulation and along a vertical line

The Fourier coefficients `fourierCoeffOn hab f n` of any function on an interval `[a, b]` tend to
`0` as `n → ±∞`. They are the Fourier transform of `f` restricted to `(a, b]` at the frequency
`n / (b - a)`, and these frequencies leave every compact set.

Testing a function on the vertical line `Re s = c` against a Dirichlet series produces the
oscillating factor `x ^ (i t)`, which is the Fourier character of frequency `-(2π)⁻¹ log x` in
the variable `t`. Letting `x → ∞` therefore pushes the frequency out of every compact set, and the
Riemann--Lebesgue lemma makes the integral vanish.

The same factor has modulus `1` and is continuous in `t`, so it multiplies an integrable function
into an integrable one, also after multiplying by a bounded continuous function such as the
simple-pole factor `1 / (σ + i t - 1)` for `σ > 1`.

## Main declarations

* `TauCeti.tendsto_fourierCoeffOn`: the Fourier coefficients on an interval tend to `0` along
  the cofinite filter on `ℤ`.
* `MeasureTheory.Integrable.tendsto_integral_sin_smul_atTop`: sine-modulated integrals
  tend to zero as the real frequency tends to positive infinity.

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

/-- **Riemann--Lebesgue for Fourier coefficients on an interval**: the coefficients
`fourierCoeffOn hab f n` tend to `0` as `n → ±∞`.

No hypothesis is needed on `f`: when `f` is not integrable on `[a, b]`, every coefficient is `0`. -/
theorem tendsto_fourierCoeffOn {a b : ℝ} (hab : a < b) (f : ℝ → E) :
    Tendsto (fourierCoeffOn hab f) cofinite (𝓝 0) := by
  have hT : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hfreq : Tendsto (fun n : ℤ ↦ (n : ℝ) * (b - a)⁻¹) cofinite (cocompact ℝ) :=
    (Homeomorph.mulRight₀ _ (inv_ne_zero hT)).isClosedEmbedding.tendsto_cocompact.comp
      Int.tendsto_coe_cofinite
  have h := ((Real.tendsto_integral_exp_smul_cocompact (Set.indicator (Set.Ioc a b) f)).comp
    hfreq).const_smul (1 / (b - a))
  rw [smul_zero] at h
  refine h.congr fun n ↦ ?_
  rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le hab.le,
    ← integral_indicator measurableSet_Ioc, Function.comp_apply]
  congr 1
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ Set.Ioc a b
  · simp only [Set.indicator_of_mem hx, fourier_coe_apply, Circle.smul_def, Real.fourierChar_apply]
    congr 2
    push_cast
    field_simp
  · simp [Set.indicator_of_notMem hx]

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

/-- The sine-modulated integral of an integrable function tends to zero at positive infinite
frequency. The codomain need not be complete. -/
theorem MeasureTheory.Integrable.tendsto_integral_sin_smul_atTop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {q : ℝ → E} (hq : Integrable q) :
    Tendsto (fun T : ℝ ↦ ∫ u, (Real.sin (2 * π * T * u) : ℂ) • q u) atTop (nhds 0) := by
  have hn := (Real.zero_at_infty_fourier q).mono_left atTop_le_cocompact
  have hp := (Real.zero_at_infty_fourier q).comp
    (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)
  have H := (hn.sub hp).const_smul ((2 : ℂ)⁻¹ * I)
  simp only [sub_zero, smul_zero] at H
  refine H.congr' ?_
  filter_upwards with T
  dsimp only [Function.comp_apply]
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hi (A : ℝ) : Integrable (fun u ↦ Complex.exp (((A * u : ℝ) : ℂ) * I) • q u) := by
    apply hq.bdd_smul 1 (by fun_prop)
    filter_upwards with u
    rw [norm_exp_ofReal_mul_I]
  rw [← integral_sub, ← MeasureTheory.integral_smul]
  · apply integral_congr_ae
    filter_upwards with u
    rw [← sub_smul, ← smul_assoc]
    congr 1
    have hneg : ((-2 * π * u * T : ℝ) : ℂ) * I =
        -((2 * π * T * u : ℝ) : ℂ) * I := by push_cast; ring
    have hpos : ((-2 * π * u * -T : ℝ) : ℂ) * I =
        ((2 * π * T * u : ℝ) : ℂ) * I := by push_cast; ring
    rw [hneg, hpos, Complex.ofReal_sin, smul_eq_mul]
    linear_combination -(1 / 2 : ℂ) * (Complex.two_sin ((2 * π * T * u : ℝ) : ℂ))
  · have heq : (fun u : ℝ ↦ Complex.exp ((((-2 * π * T) * u : ℝ) : ℂ) * I) • q u) =
        (fun u : ℝ ↦ Complex.exp (((-2 * π * u * T : ℝ) : ℂ) * I) • q u) := by
      ext u
      -- Match hi at frequency -2 * π * T to the input-first phase in the sine decomposition.
      rw [show (-2 * π * T) * u = -2 * π * u * T by ring]
    exact heq ▸ hi (-2 * π * T)
  · have heq : (fun u : ℝ ↦ Complex.exp ((((2 * π * T) * u : ℝ) : ℂ) * I) • q u) =
        (fun u : ℝ ↦ Complex.exp (((-2 * π * u * -T : ℝ) : ℂ) * I) • q u) := by
      ext u
      -- The reflected parameter -T supplies the opposite frequency in the second phase.
      rw [show (2 * π * T) * u = -2 * π * u * -T by ring]
    exact heq ▸ hi (2 * π * T)
