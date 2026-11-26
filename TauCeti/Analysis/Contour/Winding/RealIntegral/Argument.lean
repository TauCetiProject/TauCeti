/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Analysis.Contour.Winding.Integrand
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Log

/-!
# Angular integrals in a branch of the argument

For an absolutely continuous curve `γ : ℝ → ℂ` the real winding integrand
`realWindingIntegrand (γ t) (deriv γ t)` is the angular speed of `γ` about the origin. When `γ`
stays in the slit plane, the principal branch of the argument is continuous along `γ`, so the
angular integral is the exact difference of the endpoint arguments, with no reduction modulo
`2π`:

`∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t) = arg (γ b) - arg (γ a)`.

Corners of `γ` are allowed. Rotating `γ` by a fixed complex number selects another branch, and
applying the formula to the ratio of two curves compares their angular integrals.

## Main results

The argument identities are in the namespace `AbsolutelyContinuousOnInterval`.

* `ContinuousOn.intervalIntegrable_realWindingIntegrand`: a continuous nonvanishing position
  and an interval-integrable velocity have interval-integrable real winding integrand.
* `integral_realWindingIntegrand_eq_arg_sub_arg`: the angular integral
  of an absolutely continuous curve in the slit plane is the difference of the endpoint arguments.
* `integral_realWindingIntegrand_eq_arg_mul_sub_arg_mul`: the same after a
  rotation `c * γ` into the slit plane.
* `integral_realWindingIntegrand_sub_integral_realWindingIntegrand_eq_arg_div_sub_arg_div`:
  for two absolutely continuous curves whose
  ratio stays in the slit plane, the difference of their angular integrals is the change of the
  argument of the ratio.

All four results apply to piecewise `C¹` curves via
`TauCeti.IsPiecewiseC1On.absolutelyContinuousOnInterval` and its continuity and derivative
integrability consequences. The identities `integral_realWindingIntegrand_eq_arg_sub_arg` and
`integral_realWindingIntegrand_eq_arg_mul_sub_arg_mul` are exact, real-valued counterparts at
basepoint `w = 0` of `AbsolutelyContinuousOnInterval.coe_two_pi_mul_re_windingNumber`, which
identifies that quantity only as a `Real.Angle`.

On a slit-plane arc of a unit tangent, these identities identify the increment of its real
argument lift with its angular integral; the ratio formula compares such increments in two frames.
-/

public section

open Complex MeasureTheory Set intervalIntegral TauCeti.Contour

/-- A continuous nonvanishing position and an interval-integrable velocity have an
interval-integrable real winding integrand. The velocity need not be the position's derivative. -/
theorem ContinuousOn.intervalIntegrable_realWindingIntegrand
    {z v : ℝ → ℂ} {a b : ℝ} {μ : Measure ℝ}
    (hz : ContinuousOn z (uIcc a b)) (hne : ∀ t ∈ uIcc a b, z t ≠ 0)
    (hv : IntervalIntegrable v μ a b) :
    IntervalIntegrable (fun t ↦ realWindingIntegrand (z t) (v t)) μ a b := by
  have h := hv.continuousOn_mul (hz.inv₀ hne)
  simp only [realWindingIntegrand_def]
  exact ⟨h.1.im, h.2.im⟩

namespace AbsolutelyContinuousOnInterval

variable {γ η : ℝ → ℂ} {a b : ℝ}

/-- **Angular integrals of two curves with a slit-plane ratio.** For two absolutely continuous
curves `γ` and `η` whose ratio `γ / η` stays in `Complex.slitPlane`, the difference of their angular
integrals is the change of the principal argument of the ratio. -/
theorem integral_realWindingIntegrand_sub_integral_realWindingIntegrand_eq_arg_div_sub_arg_div
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hη : AbsolutelyContinuousOnInterval η a b)
    (hslit : ∀ t ∈ uIcc a b, γ t / η t ∈ slitPlane) :
    (∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t)) -
        ∫ t in a..b, realWindingIntegrand (η t) (deriv η t) =
      (γ b / η b).arg - (γ a / η a).arg := by
  have hne : ∀ t ∈ uIcc a b, γ t ≠ 0 ∧ η t ≠ 0 := fun t ht ↦
    div_ne_zero_iff.mp (slitPlane_ne_zero (hslit t ht))
  have hint := hγ.integral_deriv_div_sub_integral_deriv_div_eq_log_div_sub_log_div hη hslit
  have hγint := hγ.intervalIntegrable_deriv_div fun t ht ↦ (hne t ht).1
  have hηint := hη.intervalIntegrable_deriv_div fun t ht ↦ (hne t ht).2
  have him := congrArg im hint
  simp only [Complex.sub_im] at him
  simp only [← RCLike.im_to_complex] at him
  rw [← intervalIntegral_im hγint, ← intervalIntegral_im hηint] at him
  simpa only [RCLike.im_to_complex, realWindingIntegrand_def, div_eq_inv_mul, log_im] using him

/-- **Angular integral in the slit plane.** The angular integral of an absolutely continuous curve
staying in `Complex.slitPlane` is the difference of the principal arguments of its endpoints. -/
theorem integral_realWindingIntegrand_eq_arg_sub_arg
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hslit : ∀ t ∈ uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t) = (γ b).arg - (γ a).arg := by
  have hint := hγ.integral_deriv_div_eq_log_sub_log hslit
  have hint' := hγ.intervalIntegrable_deriv_div fun t ht ↦ slitPlane_ne_zero (hslit t ht)
  have him := congrArg im hint
  simp only [Complex.sub_im, log_im] at him
  simp only [← RCLike.im_to_complex] at him
  rw [← intervalIntegral_im hint'] at him
  simpa only [RCLike.im_to_complex, realWindingIntegrand_def, div_eq_inv_mul] using him

/-- **Angular integral after a rotation.** If a fixed multiple `c * γ` of an absolutely continuous
curve stays in `Complex.slitPlane`, the angular integral of `γ` is the change of the principal
argument of `c * γ`. -/
theorem integral_realWindingIntegrand_eq_arg_mul_sub_arg_mul
    (hγ : AbsolutelyContinuousOnInterval γ a b) {c : ℂ}
    (hslit : ∀ t ∈ uIcc a b, c * γ t ∈ slitPlane) :
    ∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t) = (c * γ b).arg - (c * γ a).arg := by
  have hc : c ≠ 0 := left_ne_zero_of_mul (slitPlane_ne_zero (hslit a left_mem_uIcc))
  have h := (hγ.const_smul c).integral_realWindingIntegrand_eq_arg_sub_arg hslit
  simpa only [smul_eq_mul, deriv_const_mul_field', realWindingIntegrand_mul_mul hc] using h

end AbsolutelyContinuousOnInterval
