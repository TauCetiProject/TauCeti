/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import Mathlib.Geometry.Manifold.Instances.Sphere

import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace
import TauCeti.Topology.Circle.Arc

/-!
# The angular form on the circle, its de Rham class and its integral

The angular form `dθ` on the unit circle `S¹ ⊆ ℂ` is the pullback, along the inclusion, of the
`1`-form `x dy − y dx` on the plane `ℂ = ℝ²`. It is a smooth form on `S¹`, and it is closed for
dimension reasons: every `1`-form on a `1`-dimensional manifold is closed.

Along the standard parametrization `t ↦ exp (t i)` of the circle, the angular form integrates to
the length of the parameter interval (`TauCeti.pathIntegral_circleAngularForm_circleExp`). The
loop over `[0, 2π]` therefore has period `2π ≠ 0`, whereas exact forms integrate to zero around
closed curves. Hence `dθ` is closed but not exact, and its class in `H¹_dR(S¹)` is nonzero: the
circle has nontrivial first de Rham cohomology, unlike the normed spaces of
`TauCeti.subsingleton_deRhamCohomology_normedSpace`.

The angular form vanishes nowhere, so it orients the circle (`TauCeti.circleOrientation`, the
counterclockwise orientation). Computing through the positively oriented parametrization
`z ↦ exp (z₀ i)` of the circle minus one point, the oriented integral of `dθ` is `2π`, and its
absolute value is `2π` for either orientation of the circle.

## Main declarations

* `TauCeti.planeAngularForm`: the `1`-form `x dy − y dx` on `ℂ`.
* `TauCeti.circleAngularForm`: the angular form `dθ` on `Circle`, its pullback along the
  inclusion.
* `TauCeti.circleAngularClosedForm`: `dθ` as a smooth closed form.
* `TauCeti.pathIntegral_circleAngularForm_circleExp`: `∫_{exp (· i)} dθ = b − a` over `a..b`.
* `TauCeti.circleAngularClosedForm_notMem_exactForms`: `dθ` is not exact.
* `TauCeti.deRhamCohomology.mk_circleAngularClosedForm_ne_zero`: `[dθ] ≠ 0` in `H¹_dR(S¹)`.
* `TauCeti.circleOrientation`: the orientation of the circle on which `dθ` is positive.
* `TauCeti.integralTopForm_circleOrientation_circleAngularForm`: `∫_{S¹} dθ = 2π`.
* `TauCeti.abs_integralTopForm_circleAngularForm`: `|∫_{S¹} dθ| = 2π` for every orientation.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (line integrals, closed
  and exact covector fields), Chapter 15 (orientations from nonvanishing top forms), Chapter 16
  (integration of top forms over parametrizations) and Chapter 17.
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
def circleAngularClosedForm : closedForms (𝓡 1) Circle 1 :=
  ⟨⟨circleAngularForm, isSmoothForm_circleAngularForm.mem_smoothBundleForms⟩,
    mem_closedForms_of_finrank_le (𝓡 1) (by simp) _⟩

/-- The underlying rough form of `circleAngularClosedForm` is `circleAngularForm`. -/
@[simp]
theorem coe_circleAngularClosedForm :
    ((circleAngularClosedForm : SmoothForm (𝓡 1) Circle ℝ 1) : RoughForm (𝓡 1) Circle ℝ 1) =
      circleAngularForm :=
  (rfl)

/-- The angular form takes the value `1` on the velocity of the standard parametrization
`t ↦ exp (t i)` of the circle. -/
theorem circleAngularForm_apply_curveVelocity_circleExp (t : ℝ) :
    circleAngularForm (Circle.exp t) (fun _ ↦ Manifold.curveVelocity (𝓡 1) Circle.exp t) =
      (1 : ℝ) := by
  -- in the plane, the velocity of `t ↦ exp (t i)` is `i exp (t i)`
  have hd : HasDerivAt (fun s : ℝ ↦ Complex.exp (s * Complex.I))
      (Complex.exp (t * Complex.I) * Complex.I) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
  -- and `dθ` evaluates to `cos² t + sin² t = 1` on it
  have h1 : (Complex.exp (t * Complex.I)).re * (Complex.exp (t * Complex.I) *
      Complex.I).im - (Complex.exp (t * Complex.I)).im *
        (Complex.exp (t * Complex.I) * Complex.I).re = 1 := by
    simp only [Complex.mul_I_re, Complex.mul_I_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.cos_sq_add_sin_sq t]
  have hv : Manifold.curveVelocity 𝓘(ℝ, ℂ) ((fun z : Circle ↦ (z : ℂ)) ∘ Circle.exp) t =
      mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (Circle.exp t)
        (Manifold.curveVelocity (𝓡 1) Circle.exp t) := by
    have hc : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (Circle.exp t) :=
      (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
    simpa only [Manifold.curveVelocityWithin_univ] using
      Manifold.curveVelocityWithin_map (s := Set.univ) hc uniqueDiffWithinAt_univ
        ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
  rw [circleAngularForm_def, mpullback_apply]
  simp only [← hv]
  simp only [Manifold.curveVelocity_eq_deriv, Function.comp_def, Circle.coe_exp, hd.deriv]
  exact (planeAngularForm_apply _ _).trans h1

/-- Along the standard parametrization `t ↦ exp (t i)` of the circle, the angular form integrates
to the length of the oriented parameter interval. -/
theorem pathIntegral_circleAngularForm_circleExp (a b : ℝ) :
    pathIntegral circleAngularForm Circle.exp a b = b - a := by
  rw [pathIntegral_def]
  simp only [circleAngularForm_apply_curveVelocity_circleExp]
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- The angular form vanishes nowhere on the circle. -/
theorem circleAngularForm_ne_zero (z : Circle) : circleAngularForm z ≠ 0 := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  intro h
  have h1 := circleAngularForm_apply_curveVelocity_circleExp t
  rw [h] at h1
  simp at h1

/-- The angular form is not exact: its period around the circle is `2π ≠ 0`. -/
theorem circleAngularClosedForm_notMem_exactForms :
    (circleAngularClosedForm : SmoothForm (𝓡 1) Circle ℝ 1) ∉ exactForms (𝓡 1) Circle 1 := by
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
instance nontrivial_deRhamCohomology_circle_one : Nontrivial (deRhamCohomology (𝓡 1) Circle 1) :=
  ⟨⟨_, 0, deRhamCohomology.mk_circleAngularClosedForm_ne_zero⟩⟩

/-! ### The orientation of the circle and the integral of the angular form -/

/-- The counterclockwise orientation of the circle: the orientation on which the nowhere-vanishing
angular form is positive. -/
def circleOrientation : Manifold.Orientation (𝓡 1) Circle (Fin 1) :=
  Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin circleAngularForm
    (isSmoothForm_circleAngularForm.of_le zero_le) circleAngularForm_ne_zero

/-- A tangent basis of the circle is positive for `circleOrientation` exactly when the angular
form is positive on it. -/
theorem orientation_eq_orientationAt_circleOrientation_iff {z : Circle}
    (b : Module.Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z)) :
    b.orientation = circleOrientation.orientationAt z ↔ 0 < circleAngularForm z b :=
  Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b

/-- The angular form is homogeneous of degree one in a multiple of the velocity of
`t ↦ exp (t i)`. -/
private theorem circleAngularForm_apply_smul_curveVelocity_circleExp (t c : ℝ) :
    circleAngularForm (Circle.exp t)
      (fun _ ↦ c • Manifold.curveVelocity (𝓡 1) Circle.exp t) = c := by
  have h := (circleAngularForm (Circle.exp t)).map_smul_univ (fun _ ↦ c)
    (fun _ ↦ Manifold.curveVelocity (𝓡 1) Circle.exp t)
  rw [circleAngularForm_apply_curveVelocity_circleExp] at h
  simpa using h

/-! The parametrization `z ↦ exp (z₀ i)` of the circle by the Euclidean line, used to compute
the integral of the angular form. -/

/-- The derivative of `z ↦ exp (z₀ i)` at `z`: `w ↦ w₀ v`, for the velocity `v` of
`t ↦ exp (t i)` at `z₀`. -/
private def circleParamDeriv (z : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((1 : ℝ →L[ℝ] ℝ).smulRight (Manifold.curveVelocity (𝓡 1) Circle.exp (z 0))).comp
    (EuclideanSpace.proj 0)

private theorem circleParamDeriv_apply (z w : EuclideanSpace ℝ (Fin 1)) :
    circleParamDeriv z w = w 0 • Manifold.curveVelocity (𝓡 1) Circle.exp (z 0) :=
  (rfl)

/-- The angular form reads off the coordinate of a vector from its image under the derivative of
the parametrization. -/
private theorem circleAngularForm_apply_circleParamDeriv (z w : EuclideanSpace ℝ (Fin 1)) :
    circleAngularForm (Circle.exp (z 0)) (fun _ ↦ circleParamDeriv z w) = w 0 := by
  simp only [circleParamDeriv_apply, circleAngularForm_apply_smul_curveVelocity_circleExp]

private theorem injective_circleParamDeriv (z : EuclideanSpace ℝ (Fin 1)) :
    Function.Injective (circleParamDeriv z) := by
  refine (injective_iff_map_eq_zero _).mpr fun w hw ↦ ?_
  have h0 := circleAngularForm_apply_circleParamDeriv z w
  rw [hw] at h0
  ext j
  rw [Subsingleton.elim j 0, ← h0]
  exact (circleAngularForm _).map_zero

/-- The derivative of the parametrization as an isomorphism onto the tangent space. -/
private def circleParamDerivEquiv (z : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) ≃L[ℝ] TangentSpace (𝓡 1) (Circle.exp (z 0)) :=
  (LinearEquiv.ofInjectiveEndo (circleParamDeriv z).toLinearMap
    (injective_circleParamDeriv z)).toContinuousLinearEquiv

private theorem circleParamDerivEquiv_apply (z w : EuclideanSpace ℝ (Fin 1)) :
    circleParamDerivEquiv z w = circleParamDeriv z w :=
  -- Both `toContinuousLinearEquiv` and `ofInjectiveEndo` keep the underlying function.
  rfl

private theorem hasMFDerivAt_circleParam (z : EuclideanSpace ℝ (Fin 1)) :
    HasMFDerivAt (𝓡 1) (𝓡 1) (fun w : EuclideanSpace ℝ (Fin 1) ↦ Circle.exp (w 0)) z
      ((circleParamDerivEquiv z).toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace z).toContinuousLinearMap) := by
  have h := (Manifold.hasMFDerivAt_curveVelocity
    ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero)).comp z
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasMFDerivAt
  have heq : (circleParamDerivEquiv z).toContinuousLinearMap.comp
      (NormedSpace.fromTangentSpace z).toContinuousLinearMap = circleParamDeriv z := by
    ext w
    exact circleParamDerivEquiv_apply z w
  rw [heq]
  -- `circleParamDeriv z` is by definition the composite derivative of `Circle.exp ∘ proj 0`.
  exact h

/-- On the image of the standard basis vector, the angular form takes the value `1`. -/
private theorem circleAngularForm_apply_circleParamDerivEquiv (z : EuclideanSpace ℝ (Fin 1)) :
    circleAngularForm (Circle.exp (z 0))
      (fun i ↦ circleParamDerivEquiv z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i)) =
        (1 : ℝ) := by
  have h (i : Fin 1) : circleParamDerivEquiv z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i) =
      circleParamDeriv z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0) := by
    rw [circleParamDerivEquiv_apply, Subsingleton.elim i 0]
  simp only [h, circleAngularForm_apply_circleParamDeriv]
  simp

/-- The parametrization is positively oriented for `circleOrientation`. -/
private theorem map_circleParamDerivEquiv_orientation (z : EuclideanSpace ℝ (Fin 1)) :
    Orientation.map (Fin 1) (circleParamDerivEquiv z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
      circleOrientation.orientationAt (Circle.exp (z 0)) := by
  rw [← Module.Basis.orientation_map, orientation_eq_orientationAt_circleOrientation_iff]
  have hmap : ⇑((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.map
      (circleParamDerivEquiv z).toLinearEquiv) =
        fun i ↦ circleParamDerivEquiv z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i) := by
    funext i
    rw [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
  rw [hmap, circleAngularForm_apply_circleParamDerivEquiv]
  exact one_pos

/-- The parametrization covers the circle minus one point, injectively. -/
private theorem image_circleParam :
    (fun z : EuclideanSpace ℝ (Fin 1) ↦ Circle.exp (z 0)) ''
        ((EuclideanSpace.proj 0) ⁻¹' Set.Ioo (-Real.pi) Real.pi) =
      {Circle.exp (-Real.pi)}ᶜ := by
  have hsurj : Function.Surjective (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) := fun t ↦
    ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t), rfl⟩
  have h := compl_circleExp_image_Icc (a := -Real.pi) (b := -Real.pi) le_rfl
    (by linarith [Real.pi_pos])
  rw [Set.Icc_self, Set.image_singleton, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  -- The parametrization factors through the coordinate projection, which is surjective.
  rw [h, show (fun z : EuclideanSpace ℝ (Fin 1) ↦ Circle.exp (z 0)) =
    Circle.exp ∘ EuclideanSpace.proj 0 from rfl, Set.image_comp, Set.image_preimage_eq _ hsurj]

private theorem injOn_circleParam :
    Set.InjOn (fun z : EuclideanSpace ℝ (Fin 1) ↦ Circle.exp (z 0))
      ((EuclideanSpace.proj 0) ⁻¹' Set.Ioo (-Real.pi) Real.pi) := by
  intro x hx y hy hxy
  have h := Circle.exp_injOn_Ioc (a := -Real.pi) (b := Real.pi) (by linarith)
    (Set.Ioo_subset_Ioc_self hx) (Set.Ioo_subset_Ioc_self hy) hxy
  ext j
  rw [Subsingleton.elim j 0]
  exact h

/-- The parameter domain `(-π, π)` of the parametrization has volume `2π`. -/
private theorem volume_preimage_proj_Ioo_neg_pi_pi :
    MeasureTheory.volume ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) ⁻¹'
      Set.Ioo (-Real.pi) Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
  rw [(TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).measure_preimage
    measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
  congr 1
  ring

/-- The integral of the angular form over the counterclockwise circle is `2π`. -/
theorem integralTopForm_circleOrientation_circleAngularForm :
    integralTopForm circleOrientation circleAngularForm = 2 * Real.pi := by
  obtain ⟨l, hl⟩ := circleOrientation.exists_lift
  have hc : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin 1]→L[ℝ] ℝ)
      circleAngularForm) :=
    isCompact_univ.of_isClosed_subset (_root_.isClosed_tsupport _) (Set.subset_univ _)
  have hD : MeasurableSet ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) ⁻¹'
      Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable
  have h := integralTopForm_eq_oriented_parametrization l circleAngularForm
    (isSmoothForm_circleAngularForm.integrableTopForm hc
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis)
    hD image_circleParam injOn_circleParam circleParamDerivEquiv
    (fun z _ ↦ hasMFDerivAt_circleParam z)
    (fun z _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl, map_circleParamDerivEquiv_orientation])
  rw [← hl, h.2, MeasureTheory.setIntegral_congr_fun hD fun z _ ↦
      circleAngularForm_apply_circleParamDerivEquiv z]
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    volume_preimage_proj_Ioo_neg_pi_pi]
  simp [Real.pi_pos.le]

/-- The angular form integrates to `±2π` over the circle, the sign being that of the
orientation. -/
theorem abs_integralTopForm_circleAngularForm (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) :
    |integralTopForm o circleAngularForm| = 2 * Real.pi := by
  rcases o.eq_or_eq_neg circleOrientation with rfl | rfl
  · rw [integralTopForm_circleOrientation_circleAngularForm, abs_of_pos Real.two_pi_pos]
  · rw [integralTopForm_neg, abs_neg, integralTopForm_circleOrientation_circleAngularForm,
      abs_of_pos Real.two_pi_pos]

end TauCeti
