/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic

/-!
# Signed area of a plane curve

For a plane curve `γ = x + i y : ℝ → ℂ` on `[a, b]`, its **signed area** is the boundary integral
`½ ∫ₐᵇ (x y' - y x')` (`TauCeti.signedArea`), the circulation of the area form
`(x dy - y dx) / 2` along `γ` (`TauCeti.signedArea_eq_integral_circulationFun`). For a circle
traversed once counterclockwise, from any initial angle, it is the area of the disc
(`TauCeti.signedArea_circleMap`).

The area–energy inequality bounding the signed area of a closed curve by its energy is in
`TauCeti.Analysis.Fourier.AreaEnergy`.

## Main definitions

* `TauCeti.signedArea`: the signed area `½ ∫ (x y' - y x')` of a plane curve on an interval.
-/

public section

open MeasureTheory Set intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b : ℝ}

/-- The **signed area** `½ ∫ₐᵇ (x y' - y x')` of the plane curve `γ = x + i y` on `[a, b]`,
computed from its velocity `deriv γ`. For an absolutely continuous curve any almost-everywhere
derivative may be used in place of `deriv γ` (`TauCeti.signedArea_eq_of_ae_hasDerivAt`). -/
noncomputable def signedArea (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  (∫ t in a..b, ((γ t).re * (deriv γ t).im - (γ t).im * (deriv γ t).re)) / 2

/-- The defining formula of `TauCeti.signedArea`. -/
theorem signedArea_def (γ : ℝ → ℂ) (a b : ℝ) :
    signedArea γ a b =
      (∫ t in a..b, ((γ t).re * (deriv γ t).im - (γ t).im * (deriv γ t).re)) / 2 :=
  (rfl)

/-- A constant curve has signed area zero. -/
@[simp]
theorem signedArea_const (c : ℂ) (a b : ℝ) : signedArea (fun _ ↦ c) a b = 0 := by
  simp [signedArea_def]

/-- The signed area over a degenerate interval is zero. -/
@[simp]
theorem signedArea_self (γ : ℝ → ℂ) (a : ℝ) : signedArea γ a a = 0 := by
  simp [signedArea_def]

/-- Reversing the interval of integration negates the signed area. -/
theorem signedArea_symm (γ : ℝ → ℂ) (a b : ℝ) : signedArea γ b a = -signedArea γ a b := by
  rw [signedArea_def, signedArea_def, integral_symm, neg_div]

/-- The signed area may be computed from any almost-everywhere derivative of the curve. -/
theorem signedArea_eq_of_ae_hasDerivAt {γ γ' : ℝ → ℂ}
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) :
    signedArea γ a b =
      (∫ t in a..b, ((γ t).re * (γ' t).im - (γ t).im * (γ' t).re)) / 2 := by
  rw [signedArea_def, intervalIntegral.integral_congr_ae]
  filter_upwards [hγ'] with t ht hmem
  rw [(ht hmem).deriv]

/-- The signed area is the circulation along `γ` of the area form `(x dy - y dx) / 2`, whose
coefficients are `TauCeti.Green.Examples.areaP` and `TauCeti.Green.Examples.areaQ`. -/
theorem signedArea_eq_integral_circulationFun (γ : ℝ → ℂ) (a b : ℝ) :
    signedArea γ a b =
      ∫ t in a..b, Green.circulationFun Green.Examples.areaP Green.Examples.areaQ γ t := by
  rw [signedArea_def, ← intervalIntegral.integral_div]
  congr 1
  funext t
  simp only [Green.circulationFun, Green.Examples.areaP_apply, Green.Examples.areaQ_apply]
  ring

/-- A circle of radius `R`, traversed once counterclockwise from any initial angle `θ`, has signed
area `π R²`. -/
@[simp]
theorem signedArea_circleMap (c : ℂ) (R θ : ℝ) :
    signedArea (circleMap c R) θ (θ + 2 * π) = π * R ^ 2 := by
  rw [signedArea_eq_of_ae_hasDerivAt (γ' := fun t ↦ circleMap 0 R t * Complex.I)
    (Filter.Eventually.of_forall fun t _ ↦ hasDerivAt_circleMap c R t)]
  -- The integrand is `R² + R (c.re cos t + c.im sin t)`; the trigonometric part has zero
  -- integral over a full period.
  have h (t : ℝ) : (circleMap c R t).re * (circleMap 0 R t * Complex.I).im -
      (circleMap c R t).im * (circleMap 0 R t * Complex.I).re =
      R ^ 2 + R * c.re * Real.cos t + R * c.im * Real.sin t := by
    simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq t]
  simp_rw [h]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cos,
    integral_sin, Real.sin_add_two_pi, Real.cos_add_two_pi]
  simp
  ring

end TauCeti
