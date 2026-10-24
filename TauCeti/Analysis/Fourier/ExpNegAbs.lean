/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Fourier transform and decay of the two-sided exponential

For `0 < a` the function `x ↦ exp (-(a * |x|))` on `ℝ` is integrable, and pairing it against the
oscillation `exp (b * x * I)` produces the Lorentzian `2 * a / (a ^ 2 + b ^ 2)`. In Mathlib's
normalisation `𝓕 f ξ = ∫ x, exp (-2 π i x ξ) f x` this reads

`𝓕 (fun x ↦ exp (-(a * |x|))) ξ = 2 * a / (a ^ 2 + (2 * π * ξ) ^ 2)`.

The proof splits the line at the origin, where `|x|` becomes `∓x`, and evaluates the two
resulting complex exponential integrals with `integral_exp_mul_complex_Iic` and
`integral_exp_mul_complex_Ioi`.

The two-sided exponential also decays faster than every real power at both ends of
the line. Its real- and complex-valued forms supply decay estimates for Fourier analysis.

## Main results

* `TauCeti.integral_exp_mul_I_mul_exp_neg_mul_abs`: the Lorentzian pairing;
* `TauCeti.fourier_exp_neg_mul_abs`: the Fourier transform itself;
* `TauCeti.cexp_neg_mul_abs_isLittleO_rpow_cocompact`: decay with a complex rate of
  positive real part;
* `TauCeti.ofReal_exp_neg_mul_abs_isLittleO_rpow_cocompact`: the complex-valued form of
  the real exponential used by the Fourier transform.
-/

public section

open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform Real

namespace TauCeti

variable {a : ℝ}

/-- **The Lorentzian pairing of the two-sided exponential with a complex oscillation.** -/
theorem integral_exp_mul_I_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      = ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  -- Rewrite the integrand as a single complex exponential on each half-line.
  have hre₁ : ((a : ℂ) + b * Complex.I).re = a := by simp
  have hre₂ : (-(a : ℂ) + b * Complex.I).re = -a := by simp
  have key : ∀ c x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (c * x) : ℂ)
      = Complex.exp (((c : ℂ) + b * Complex.I) * x) := by
    intro c x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp (((a : ℂ) + b * Complex.I) * x)) (Iic 0) := by
    intro x hx
    have hxa : -(a * |x|) = a * x := by rw [abs_of_nonpos (mem_Iic.mp hx)]; ring
    simpa only [hxa] using key a x
  have hp : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp ((-(a : ℂ) + b * Complex.I) * x)) (Ioi 0) := by
    intro x hx
    have hxa : -(a * |x|) = -a * x := by rw [abs_of_pos (mem_Ioi.mp hx)]; ring
    simpa only [hxa, Complex.ofReal_neg] using key (-a) x
  -- Integrability comes from the real two-sided exponential, since the oscillation has norm one.
  have hint : Integrable
      (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      := ((integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) (by fun_prop)
        (.of_forall fun x ↦ by simp [Complex.norm_exp])
  have hne₁ : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₁
    exact ha.ne' (by simpa using hre₁.symm)
  have hne₂ : -(a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₂
    simp only [Complex.zero_re] at hre₂
    exact ha.ne' (by linarith)
  have hsq : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
  -- Evaluate the two half-line integrals and combine the resulting rational functions.
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    setIntegral_congr_fun measurableSet_Iic hm, setIntegral_congr_fun measurableSet_Ioi hp,
    integral_exp_mul_complex_Iic (by rw [hre₁]; exact ha),
    integral_exp_mul_complex_Ioi (by rw [hre₂]; linarith)]
  have hprod : ((a : ℂ) + b * Complex.I) * (-(a : ℂ) + b * Complex.I)
      = -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
    linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have hdenom : ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : ((a ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
    push_cast at this
    exact this
  rw [Complex.ofReal_div]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (-2 * (a : ℂ)) * hprod

/-- **The Fourier transform of the two-sided exponential.** With Mathlib's normalisation
`𝓕 f ξ = ∫ x, exp (-2 π i x ξ) f x`, the transform of `x ↦ exp (-(a * |x|))` is the Lorentzian
`2 * a / (a ^ 2 + (2 * π * ξ) ^ 2)`. -/
theorem fourier_exp_neg_mul_abs (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (Real.exp (-(a * |x|)) : ℂ)) ξ
      = ((2 * a / (a ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  -- Unfold the real inner product and scalar action to match the oscillatory-integral lemma.
  calc
    _ = ∫ x : ℝ, Complex.exp (((-(2 * π * ξ) : ℝ) : ℂ) * x * Complex.I) *
        (Real.exp (-(a * |x|)) : ℂ) := integral_congr_ae (.of_forall fun x ↦ by
      change Complex.exp ((↑(-2 * π * (inner ℝ x ξ : ℝ)) * Complex.I)) •
        (Real.exp (-(a * |x|)) : ℂ) = _
      rw [smul_eq_mul]
      congr 2
      push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring)
    _ = _ := by
      rw [integral_exp_mul_I_mul_exp_neg_mul_abs ha]
      norm_num

/-- **Two-sided complex exponential decay beats every real power.** If a complex rate
has positive real part, then `exp (-(a * |x|))` is little-o of `|x| ^ s` as
`|x|` tends to infinity, for every real `s`.

The real-valued estimate is `exp_neg_mul_abs_isLittleO_rpow_cocompact`. -/
theorem cexp_neg_mul_abs_isLittleO_rpow_cocompact
    {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (fun x : ℝ => Complex.exp (-(a * |x|)))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simpa only [Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal] using
    (exp_neg_mul_abs_isLittleO_rpow_cocompact ha s)

/-- **Fourier-compatible complex-valued exponential decay.** For a positive real rate,
the complex embedding of `Real.exp (-(a * |x|))` is little-o of any real power of `|x|`.
This is the symbol used by `fourier_exp_neg_mul_abs`. -/
theorem ofReal_exp_neg_mul_abs_isLittleO_rpow_cocompact
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => (Real.exp (-(a * |x|)) : ℂ))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using
    (exp_neg_mul_abs_isLittleO_rpow_cocompact ha s)

end TauCeti
