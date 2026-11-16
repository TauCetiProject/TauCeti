/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.Contour.LogDerivFTC
public import TauCeti.Analysis.Contour.Winding.Integrand
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Angular integrals in a branch of the argument

For a piecewise `C¹` curve `γ : ℝ → ℂ` the real winding integrand
`realWindingIntegrand (γ t) (deriv γ t)` is the angular speed of `γ` about the origin. When `γ`
stays in the slit plane, the principal branch of the argument is continuous along `γ`, so the
angular integral is the exact difference of the endpoint arguments, with no reduction modulo
`2π`:

`∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t) = arg (γ b) - arg (γ a)`.

Corners of `γ` are allowed. Rotating `γ` by a fixed complex number selects another branch, and
applying the formula to the ratio of two curves compares their angular integrals.

## Main results

* `TauCeti.IsPiecewiseC1On.intervalIntegrable_realWindingIntegrand`: the angular speed of a
  piecewise `C¹` curve avoiding the origin is interval integrable.
* `TauCeti.IsPiecewiseC1On.integral_realWindingIntegrand_eq_arg_sub`: the angular integral of a
  piecewise `C¹` curve in the slit plane is the difference of the endpoint arguments.
* `TauCeti.IsPiecewiseC1On.integral_realWindingIntegrand_eq_arg_mul_sub`: the same after a
  rotation `c * γ` into the slit plane.
* `TauCeti.Contour.integral_realWindingIntegrand_sub_eq_arg_div_sub`: for two `C¹` curves whose
  ratio stays in the slit plane, the difference of their angular integrals is the change of the
  argument of the ratio.

The second and third are exact, real-valued counterparts of
`TauCeti.IsPiecewiseC1On.coe_two_pi_mul_re_windingNumber`, which identifies the same quantity
only as a `Real.Angle`.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2
  (1935), 50–62.
-/

public section

open Complex MeasureTheory Set intervalIntegral

namespace TauCeti.Contour

variable {γ η : ℝ → ℂ} {a b : ℝ}

/-- The angular speed `realWindingIntegrand (γ t) (deriv γ t)` of a piecewise `C¹` curve that
avoids the origin is interval integrable. -/
theorem _root_.TauCeti.IsPiecewiseC1On.intervalIntegrable_realWindingIntegrand
    (hγ : IsPiecewiseC1On γ a b) (hne : ∀ t ∈ uIcc a b, γ t ≠ 0) :
    IntervalIntegrable (fun t ↦ realWindingIntegrand (γ t) (deriv γ t)) volume a b := by
  have h := intervalIntegrable_inv_sub_mul_deriv (w := 0) hγ.continuousOn hne
    hγ.intervalIntegrable_deriv
  simpa only [realWindingIntegrand_def, sub_zero, Complex.imCLM_apply] using
    intervalIntegrable_iff.mpr (Complex.imCLM.integrable_comp h.def')

/-- **Angular integral in the slit plane.** The angular integral of a piecewise `C¹` curve
staying in `Complex.slitPlane` is the difference of the principal arguments of its endpoints. -/
theorem _root_.TauCeti.IsPiecewiseC1On.integral_realWindingIntegrand_eq_arg_sub
    (hγ : IsPiecewiseC1On γ a b) (hslit : ∀ t ∈ uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t) = (γ b).arg - (γ a).arg := by
  obtain ⟨P, hP, hdiff⟩ := hγ.exists_countable_differentiableAt
  have hint := intervalIntegrable_inv_sub_mul_deriv (w := 0) hγ.continuousOn
    (fun t ht ↦ slitPlane_ne_zero (hslit t ht)) hγ.intervalIntegrable_deriv
  simp only [sub_zero] at hint
  have hint' : IntervalIntegrable (fun t ↦ deriv γ t / γ t) volume a b := by
    simpa only [div_eq_inv_mul] using hint
  have h := (intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane
    hP hγ.continuousOn hdiff hint' hslit (fun _ _ ↦ rfl) rfl rfl).2
  simp_rw [realWindingIntegrand_def, ← RCLike.im_to_complex]
  rw [intervalIntegral_im hint, RCLike.im_to_complex]
  simp only [← div_eq_inv_mul, h, sub_im, log_im]

/-- **Angular integral after a rotation.** If a fixed multiple `c * γ` of a piecewise `C¹` curve
stays in `Complex.slitPlane`, the angular integral of `γ` is the change of the principal argument
of `c * γ`. -/
theorem _root_.TauCeti.IsPiecewiseC1On.integral_realWindingIntegrand_eq_arg_mul_sub
    (hγ : IsPiecewiseC1On γ a b) {c : ℂ} (hslit : ∀ t ∈ uIcc a b, c * γ t ∈ slitPlane) :
    ∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t) = (c * γ b).arg - (c * γ a).arg := by
  have hc : c ≠ 0 := left_ne_zero_of_mul (slitPlane_ne_zero (hslit a left_mem_uIcc))
  have h := (hγ.const_smul c).integral_realWindingIntegrand_eq_arg_sub hslit
  simpa only [smul_eq_mul, deriv_const_mul_field', realWindingIntegrand_mul_mul hc] using h

/-- **Angular integrals of two curves with a slit-plane ratio.** For two `C¹` curves `γ` and `η`
whose ratio `η / γ` stays in `Complex.slitPlane`, the difference of their angular integrals is the
change of the principal argument of the ratio. -/
theorem integral_realWindingIntegrand_sub_eq_arg_div_sub (hγ : ContDiffOn ℝ 1 γ (uIcc a b))
    (hη : ContDiffOn ℝ 1 η (uIcc a b)) (hslit : ∀ t ∈ uIcc a b, η t / γ t ∈ slitPlane) :
    (∫ t in a..b, realWindingIntegrand (η t) (deriv η t)) -
        ∫ t in a..b, realWindingIntegrand (γ t) (deriv γ t) =
      (η b / γ b).arg - (η a / γ a).arg := by
  have hne : ∀ t ∈ uIcc a b, η t ≠ 0 ∧ γ t ≠ 0 := fun t ht ↦
    div_ne_zero_iff.mp (slitPlane_ne_zero (hslit t ht))
  have hratio : ContDiffOn ℝ 1 (fun t ↦ η t / γ t) (uIcc a b) := by
    refine (hη.mul (hγ.inv fun t ht ↦ (hne t ht).2)).congr fun t _ ↦ ?_
    simp only [Pi.inv_apply, div_eq_mul_inv]
  rw [← (IsPiecewiseC1On.of_contDiffOn hratio).integral_realWindingIntegrand_eq_arg_sub hslit,
    ← integral_sub ((IsPiecewiseC1On.of_contDiffOn hη).intervalIntegrable_realWindingIntegrand
      fun t ht ↦ (hne t ht).1)
    ((IsPiecewiseC1On.of_contDiffOn hγ).intervalIntegrable_realWindingIntegrand
      fun t ht ↦ (hne t ht).2)]
  refine integral_congr_uIoo fun t ht ↦ ?_
  have hmem : uIcc a b ∈ nhds t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
  have h := logDeriv_fun_div t (hne t (Ioo_subset_Icc_self ht)).1
    (hne t (Ioo_subset_Icc_self ht)).2 ((hη.contDiffAt hmem).differentiableAt one_ne_zero)
    ((hγ.contDiffAt hmem).differentiableAt one_ne_zero)
  simpa only [logDeriv_apply, realWindingIntegrand_def, inv_mul_eq_div, sub_im] using
    (congrArg im h).symm

end TauCeti.Contour
