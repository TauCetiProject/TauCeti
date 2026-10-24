/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import Mathlib.Geometry.Manifold.Instances.Sphere

import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The angular form on the circle and its de Rham class

The angular form `dθ` on the unit circle `S¹ ⊆ ℂ` is the pullback, along the inclusion, of the
`1`-form `x dy − y dx` on the plane `ℂ = ℝ²`. It is a smooth form on `S¹`, and it is closed for
dimension reasons: every `1`-form on a `1`-dimensional manifold is closed.

Along the standard parametrization `t ↦ exp (t i)` of the circle, the angular form integrates to
the length of the parameter interval (`TauCeti.pathIntegral_circleAngularForm_circleExp`). The
loop over `[0, 2π]` therefore has period `2π ≠ 0`, whereas exact forms integrate to zero around
closed curves. Hence `dθ` is closed but not exact, and its class in `H¹_dR(S¹)` is nonzero: the
circle has nontrivial first de Rham cohomology, unlike the normed spaces of
`TauCeti.subsingleton_deRhamCohomology_normedSpace`.

## Main declarations

* `TauCeti.planeAngularForm`: the `1`-form `x dy − y dx` on `ℂ`.
* `TauCeti.circleAngularForm`: the angular form `dθ` on `Circle`, its pullback along the
  inclusion.
* `TauCeti.circleAngularClosedForm`: `dθ` as a smooth closed form.
* `TauCeti.pathIntegral_circleAngularForm_circleExp`: `∫_{exp (· i)} dθ = b − a` over `a..b`.
* `TauCeti.circleAngularClosedForm_notMem_exactForms`: `dθ` is not exact.
* `TauCeti.deRhamCohomology.mk_circleAngularClosedForm_ne_zero`: `[dθ] ≠ 0` in `H¹_dR(S¹)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (line integrals, closed
  and exact covector fields) and Chapter 17.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- The `1`-form `x dy − y dx` on the plane `ℂ = ℝ²`, whose pullback to the unit circle is the
angular form `dθ`. -/
def planeAngularForm : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 1 :=
  fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
    (z.re • Complex.imCLM - z.im • Complex.reCLM)

/-- Evaluation of the plane angular form: `(x dy − y dx)(v) = x v_y − y v_x` at `z = x + y i`. -/
@[simp]
theorem planeAngularForm_apply (z : ℂ) (v : Fin 1 → ℂ) :
    planeAngularForm z v = z.re * (v 0).im - z.im * (v 0).re :=
  (rfl)

/-- The plane angular form is smooth. -/
theorem isSmoothForm_planeAngularForm : IsSmoothForm 𝓘(ℝ, ℂ) ∞ planeAngularForm := by
  rw [isSmoothForm_modelSpace_iff]
  refine (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ)
    (0 : Fin 1)).contDiff.comp ?_
  exact (Complex.reCLM.contDiff.smul contDiff_const).sub
    (Complex.imCLM.contDiff.smul contDiff_const)

/-- The angular form `dθ` on the unit circle: the pullback of `x dy − y dx` along the inclusion
`S¹ → ℂ`. -/
def circleAngularForm : RoughForm (𝓡 1) Circle ℝ 1 :=
  mpullback (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) planeAngularForm

/-- The angular form on the circle is the pullback of the plane angular form along the
inclusion. -/
theorem circleAngularForm_def :
    circleAngularForm = mpullback (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) planeAngularForm :=
  (rfl)

/-- The angular form on the circle is smooth. -/
theorem isSmoothForm_circleAngularForm : IsSmoothForm (𝓡 1) ∞ circleAngularForm :=
  isSmoothForm_planeAngularForm.mpullback contMDiff_coe_sphere

/-- The angular form `dθ` as a smooth closed form on the circle. It is closed because the circle
is `1`-dimensional. -/
def circleAngularClosedForm : closedForms (𝓡 1) Circle ℝ 1 :=
  ⟨⟨circleAngularForm, isSmoothForm_circleAngularForm.mem_smoothForms⟩,
    mem_closedForms_of_finrank_le (𝓡 1) (by simp) _⟩

/-- The underlying rough form of `circleAngularClosedForm` is `circleAngularForm`. -/
@[simp]
theorem coe_circleAngularClosedForm :
    ((circleAngularClosedForm : SmoothForm (𝓡 1) Circle ℝ 1) : RoughForm (𝓡 1) Circle ℝ 1) =
      circleAngularForm :=
  (rfl)

/-- Along the standard parametrization `t ↦ exp (t i)` of the circle, the angular form integrates
to the length of the oriented parameter interval. -/
theorem pathIntegral_circleAngularForm_circleExp (a b : ℝ) :
    pathIntegral circleAngularForm Circle.exp a b = b - a := by
  rw [circleAngularForm_def, pathIntegral_mpullback]
  rotate_left
  · exact fun t _ ↦ (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  · exact fun t _ ↦ (contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero
  -- in the plane, the velocity of `t ↦ exp (t i)` is `i exp (t i)`
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.exp (s * Complex.I))
      (Complex.exp (t * Complex.I) * Complex.I) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
  -- and `dθ` evaluates to `cos² t + sin² t = 1` on it
  have h1 (t : ℝ) : (Complex.exp (t * Complex.I)).re * (Complex.exp (t * Complex.I) *
      Complex.I).im - (Complex.exp (t * Complex.I)).im *
        (Complex.exp (t * Complex.I) * Complex.I).re = 1 := by
    simp only [Complex.mul_I_re, Complex.mul_I_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.cos_sq_add_sin_sq t]
  simp only [pathIntegral_def, Manifold.curveVelocity_eq_deriv, Function.comp_def, Circle.coe_exp,
    (hd _).deriv, planeAngularForm_apply, h1, intervalIntegral.integral_const, smul_eq_mul,
    mul_one]

/-- The angular form is not exact: its period around the circle is `2π ≠ 0`. -/
theorem circleAngularClosedForm_notMem_exactForms :
    (circleAngularClosedForm : SmoothForm (𝓡 1) Circle ℝ 1) ∉ exactForms (𝓡 1) Circle ℝ 1 := by
  intro h
  have h0 := pathIntegral_eq_zero_of_mem_exactForms h (contMDiff_circleExp (m := 1))
    (a := 0) (b := 2 * Real.pi) (by rw [Circle.exp_zero, Circle.exp_two_pi])
  rw [coe_circleAngularClosedForm, pathIntegral_circleAngularForm_circleExp] at h0
  linarith [Real.pi_pos]

/-- The de Rham class `[dθ]` of the angular form is nonzero in `H¹_dR(S¹)`. -/
theorem deRhamCohomology.mk_circleAngularClosedForm_ne_zero :
    deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm ≠ 0 := by
  rw [Ne, deRhamCohomology.mk_eq_zero_iff]
  exact circleAngularClosedForm_notMem_exactForms

/-- The first de Rham cohomology of the circle is nontrivial. -/
instance nontrivial_deRhamCohomology_circle_one : Nontrivial (deRhamCohomology (𝓡 1) Circle ℝ 1) :=
  ⟨⟨_, 0, deRhamCohomology.mk_circleAngularClosedForm_ne_zero⟩⟩

end TauCeti
