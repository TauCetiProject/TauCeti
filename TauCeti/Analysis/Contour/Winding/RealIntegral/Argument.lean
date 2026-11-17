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
import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
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

All results are in the namespace `AbsolutelyContinuousOnInterval`.

* `intervalIntegrable_realWindingIntegrand`: the angular speed of an
  absolutely continuous curve avoiding the origin is interval integrable.
* `integral_realWindingIntegrand_eq_arg_sub_arg`: the angular integral
  of an absolutely continuous curve in the slit plane is the difference of the endpoint arguments.
* `integral_realWindingIntegrand_eq_arg_mul_sub_arg_mul`: the same after a
  rotation `c * γ` into the slit plane.
* `integral_realWindingIntegrand_sub_integral_realWindingIntegrand_eq_arg_div_sub_arg_div`:
  for two absolutely continuous curves whose
  ratio stays in the slit plane, the difference of their angular integrals is the change of the
  argument of the ratio.

The single-curve formulas apply to piecewise `C¹` curves via
`TauCeti.IsPiecewiseC1On.absolutelyContinuousOnInterval`.
They are exact, real-valued counterparts of
`TauCeti.IsPiecewiseC1On.coe_two_pi_mul_re_windingNumber`, which identifies the same quantity
only as a `Real.Angle`.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2
  (1935), 50–62.
-/

public section

open Complex MeasureTheory Set intervalIntegral TauCeti.Contour

namespace AbsolutelyContinuousOnInterval

variable {γ η : ℝ → ℂ} {a b : ℝ}

/-- The angular speed `realWindingIntegrand (γ t) (deriv γ t)` of an absolutely continuous curve
that avoids the origin is interval integrable. -/
theorem intervalIntegrable_realWindingIntegrand
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hne : ∀ t ∈ uIcc a b, γ t ≠ 0) :
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t) (deriv γ t)) volume a b := by
  have h := hγ.intervalIntegrable_inv_sub_mul_deriv (z := 0)
    (by rintro ⟨t, ht, he⟩; exact hne t ht he)
  simpa only [realWindingIntegrand_def, sub_zero, Complex.imCLM_apply] using
    intervalIntegrable_iff.mpr (Complex.imCLM.integrable_comp h.def')

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
  have hlog := (hγ.fun_div hη fun t ht ↦ (hne t ht).2).clog hslit
  have hint := hlog.integral_eq_sub_of_ae_hasDerivAt
    (hγ.boundedVariationOn.ae_hasDerivAt_clog_div hη.boundedVariationOn hslit)
  have hγint := hγ.intervalIntegrable_inv_sub_mul_deriv (z := 0)
    (by rintro ⟨t, ht, he⟩; exact (hne t ht).1 he)
  have hηint := hη.intervalIntegrable_inv_sub_mul_deriv (z := 0)
    (by rintro ⟨t, ht, he⟩; exact (hne t ht).2 he)
  simp only [sub_zero, ← div_eq_inv_mul] at hγint hηint
  rw [integral_sub hγint hηint] at hint
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
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ (1 : ℂ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [div_one, deriv_const, realWindingIntegrand_def, mul_zero, zero_im,
    intervalIntegral.integral_zero, sub_zero] using
    hγ.integral_realWindingIntegrand_sub_integral_realWindingIntegrand_eq_arg_div_sub_arg_div
      hconst (by simpa only [div_one] using hslit)

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
