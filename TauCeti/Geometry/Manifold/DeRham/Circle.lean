/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Circle
public import TauCeti.Geometry.Manifold.Orientation.AddCircle

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace
import TauCeti.Topology.Circle.Arc

/-!
# The angular form on the circle: de Rham class, pullback calculus, integral, time coordinate

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

For any differentiable circle-valued map `f : M → Circle`, the pulled-back angular form `f^* dθ` is
the imaginary part of the logarithmic derivative `dlog f`
(`TauCeti.mpullback_circleAngularForm_apply_eq_im_mlogDeriv`). Because `dlog` turns pointwise
products into sums, pullback of `dθ` turns pointwise multiplication into addition, inversion into
negation, division into subtraction, negation into the identity, and integer powers into scalar
multiplication; on `Circle` itself, `(· ^ k)^* dθ = k • dθ`
(`TauCeti.mpullback_zpow_id_circleAngularForm`).

The standard parametrization pulls `dθ` back to `dt` on `ℝ`
(`TauCeti.mpullback_circleExp_circleAngularForm`). Through the identification
`AddCircle.toCircle : AddCircle p → Circle`, `[t] ↦ exp (2π i t / p)`, of the circle of period
`p > 0` with the unit circle (`AddCircle.diffeomorphCircle`), the angular form and the time form
`dt_p` of `AddCircle p` therefore differ by the constant factor of the angle `θ = 2π t / p`: `dθ`
pulls back to `(2π / p) dt_p` (`AddCircle.mpullback_toCircle_circleAngularForm`), and `dt_p`
corresponds to `(p / 2π) dθ` on the unit circle
(`AddCircle.mpullback_homeomorphCircle_symm_timeForm`).
In particular the time form of the unit-period circle is `dθ / 2π`. Since the factor is positive,
`toCircle` carries the positive orientation of `AddCircle p` to the counterclockwise orientation
(`AddCircle.isOrientationPreservingAt_toCircle`).

## Main declarations

* `TauCeti.planeAngularForm`: the `1`-form `x dy − y dx` on `ℂ`.
* `TauCeti.circleAngularForm`: the angular form `dθ` on `Circle`, its pullback along the
  inclusion.
* `TauCeti.circleAngularForm_apply`: evaluation of `dθ` via the ambient derivative in `ℂ`.
* `TauCeti.circleAngularClosedForm`: `dθ` as a smooth closed form.
* `TauCeti.pathIntegral_circleAngularForm_circleExp`: `∫_{exp (· i)} dθ = b − a` over `a..b`.
* `TauCeti.circleAngularClosedForm_notMem_exactForms`: `dθ` is not exact.
* `TauCeti.deRhamCohomology.mk_circleAngularClosedForm_ne_zero`: `[dθ] ≠ 0` in `H¹_dR(S¹)`.
* `TauCeti.circleOrientation`, `TauCeti.circleOrientation_def`: the orientation of the circle on
  which `dθ` is positive.
* `TauCeti.integralTopForm_circleOrientation_circleAngularForm`: `∫_{S¹} dθ = 2π`.
* `TauCeti.abs_integralTopForm_circleAngularForm`: `|∫_{S¹} dθ| = 2π` for every orientation.
* `TauCeti.mpullback_circleAngularForm_apply_eq_im_mlogDeriv`,
  `TauCeti.mpullback_mul_circleAngularForm`, `TauCeti.mpullback_inv_circleAngularForm`,
  `TauCeti.mpullback_div_circleAngularForm`, `TauCeti.mpullback_pow_circleAngularForm`,
  `TauCeti.mpullback_zpow_circleAngularForm`, `TauCeti.mpullback_neg_circleAngularForm`,
  `TauCeti.mpullback_zpow_id_circleAngularForm`: pullback calculus of `dθ` under group operations
  and integer powers.
* `TauCeti.mpullback_circleExp_circleAngularForm`: `t ↦ exp (t i)` pulls `dθ` back to `dt`.
* `AddCircle.mpullback_toCircle_circleAngularForm`: `toCircle` pulls `dθ` back to `(2π / p) dt_p`.
* `AddCircle.mpullback_homeomorphCircle_symm_timeForm`: on the unit circle, `dt_p = (p / 2π) dθ`.
* `AddCircle.isOrientationPreservingAt_toCircle`: `toCircle` preserves orientation.

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

/-- Evaluation of the angular form `dθ` on `Circle` in terms of the ambient derivative in `ℂ`. -/
@[simp]
theorem circleAngularForm_apply (z : Circle) (v : Fin 1 → TangentSpace (𝓡 1) z) :
    circleAngularForm z v =
      (z : ℂ).re * (mvfderiv (𝓡 1) (fun w : Circle ↦ (w : ℂ)) z (v 0)).im -
        (z : ℂ).im * (mvfderiv (𝓡 1) (fun w : Circle ↦ (w : ℂ)) z (v 0)).re := by
  rw [circleAngularForm_def, mpullback_apply, mvfderiv_apply_eq_mfderiv_apply]
  -- `planeAngularForm` evaluates on `TangentSpace 𝓘(ℝ, ℂ) (z : ℂ) = ℂ`, and
  -- `NormedSpace.fromTangentSpace` is the identity on `ℂ`.
  exact planeAngularForm_apply (z : ℂ) _

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
  -- in the plane, the velocity of `t ↦ exp (t i)` is `i exp (t i)`, and `dθ` evaluates to
  -- `cos² t + sin² t = 1` on it
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
  simp only [Manifold.curveVelocity_eq_deriv, Function.comp_def]
  rw [(hasDerivAt_coe_circleExp t).deriv]
  simp only [Circle.coe_exp, mul_comm Complex.I]
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

/-- The orientation `circleOrientation` is the top-form orientation attached to
`circleAngularForm`. -/
theorem circleOrientation_def :
    circleOrientation =
      Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin circleAngularForm
        (isSmoothForm_circleAngularForm.of_le zero_le) circleAngularForm_ne_zero :=
  (rfl)

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

/-- The standard parametrization `t ↦ exp (t i)` of the circle pulls the angular form `dθ` back to
the differential `dt` of the coordinate of `ℝ`. -/
@[simp]
theorem mpullback_circleExp_circleAngularForm :
    mpullback 𝓘(ℝ) (𝓡 1) Circle.exp circleAngularForm =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id) := by
  funext t
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  -- The tangent vector `v 0` of `ℝ` is a real number `w`.
  obtain ⟨w, hw⟩ : ∃ w : ℝ, v 0 = w := ⟨v 0, rfl⟩
  have hv : (fun i ↦ mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp t (v i)) =
      fun _ ↦ w • Manifold.curveVelocity (𝓡 1) Circle.exp t := by
    funext i
    rw [Subsingleton.elim i 0, hw, Manifold.mfderiv_apply_eq_smul_curveVelocity]
  rw [mpullback_apply, hv, circleAngularForm_apply_smul_curveVelocity_circleExp,
    mextDeriv_ofFunction_id_apply, hw]

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
  have h := compl_circleExp_image_Icc (-Real.pi) (-Real.pi)
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
  have h := integralTopForm_eq_oriented_parametrization l
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis circleAngularForm
    (isSmoothForm_circleAngularForm.integrableTopForm hc
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis)
    hD (Set.countable_singleton _).isNullSet image_circleParam injOn_circleParam
    circleParamDerivEquiv
    (fun z _ ↦ hasMFDerivAt_circleParam z)
    (fun z _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl, map_circleParamDerivEquiv_orientation])
  rw [OrthonormalBasis.addHaar_eq_volume] at h
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

/-! ### Pullback calculus of the angular form -/

section PullbackAngularForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- For a map `f : M → Circle` differentiable at `x`, the pulled-back angular form `f^* dθ` at `x`
is the imaginary part of the logarithmic derivative `dlog f`. -/
theorem mpullback_circleAngularForm_apply_eq_im_mlogDeriv {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (v : Fin 1 → TangentSpace I x) :
    mpullback I (𝓡 1) f circleAngularForm x v =
      (mlogDeriv I (fun y ↦ (f y : ℂ)) x v).im := by
  have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle ↦ (w : ℂ)) (f x) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have hd : mvfderiv (𝓡 1) (fun w : Circle ↦ (w : ℂ)) (f x) (mfderiv I (𝓡 1) f x (v 0)) =
      mvfderiv I (fun y ↦ (f y : ℂ)) x (v 0) :=
    (mvfderiv_comp_apply x hcoe hf (v 0)).symm
  rw [mpullback_apply, circleAngularForm_apply, hd, mlogDeriv_apply, ← Circle.coe_inv,
    Circle.coe_inv_eq_conj, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Pulling back the angular form along a constant map into `Circle` gives `0`. -/
theorem mpullback_const_circleAngularForm (z₀ : Circle) :
    mpullback I (𝓡 1) (fun _ : M ↦ z₀) circleAngularForm = 0 :=
  mpullback_const one_ne_zero z₀ _

/-- **Pullback of `dθ` turns products into sums.** If `f, g : M → Circle` are differentiable at `x`,
then `(f * g)^* dθ = f^* dθ + g^* dθ` at `x`. -/
@[to_fun mpullback_fun_mul_circleAngularForm_apply]
theorem mpullback_mul_circleAngularForm_apply {f g : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (hg : MDifferentiableAt I (𝓡 1) g x) :
    mpullback I (𝓡 1) (f * g) circleAngularForm x =
      mpullback I (𝓡 1) f circleAngularForm x + mpullback I (𝓡 1) g circleAngularForm x := by
  have hfg : MDifferentiableAt I (𝓡 1) (f * g) x :=
    ((contMDiff_mul (𝓡 1) 1).mdifferentiableAt one_ne_zero).comp x (hf.prodMk hg)
  have hcoe (w : Circle) : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) w :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have huf : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (f y : ℂ)) x := (hcoe (f x)).comp x hf
  have hug : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (g y : ℂ)) x := (hcoe (g x)).comp x hg
  ext v
  rw [mpullback_circleAngularForm_apply_eq_im_mlogDeriv hfg, ContinuousAlternatingMap.add_apply,
    mpullback_circleAngularForm_apply_eq_im_mlogDeriv hf,
    mpullback_circleAngularForm_apply_eq_im_mlogDeriv hg]
  have hmul := mlogDeriv_mul huf hug (Circle.coe_ne_zero (f x)) (Circle.coe_ne_zero (g x))
  simpa only [Pi.mul_def, Circle.coe_mul, ContinuousAlternatingMap.add_apply,
    Complex.add_im] using congrArg (fun η ↦ (η v).im) hmul

/-- For differentiable maps `f, g : M → Circle`, `(f * g)^* dθ = f^* dθ + g^* dθ`. -/
theorem mpullback_mul_circleAngularForm {f g : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (hg : MDifferentiable I (𝓡 1) g) :
    mpullback I (𝓡 1) (f * g) circleAngularForm =
      mpullback I (𝓡 1) f circleAngularForm + mpullback I (𝓡 1) g circleAngularForm :=
  funext fun x ↦ mpullback_mul_circleAngularForm_apply (hf x) (hg x)

/-- For differentiable maps `f, g : M → Circle`, `(fun y ↦ f y * g y)^* dθ = f^* dθ + g^* dθ`. -/
theorem mpullback_fun_mul_circleAngularForm {f g : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (hg : MDifferentiable I (𝓡 1) g) :
    mpullback I (𝓡 1) (fun y ↦ f y * g y) circleAngularForm =
      mpullback I (𝓡 1) f circleAngularForm + mpullback I (𝓡 1) g circleAngularForm :=
  mpullback_mul_circleAngularForm hf hg

/-- If `f : M → Circle` is differentiable at `x`, then `(f⁻¹)^* dθ = - f^* dθ` at `x`. -/
@[to_fun mpullback_fun_inv_circleAngularForm_apply]
theorem mpullback_inv_circleAngularForm_apply {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) :
    mpullback I (𝓡 1) f⁻¹ circleAngularForm x =
      -mpullback I (𝓡 1) f circleAngularForm x := by
  have hinv : MDifferentiableAt I (𝓡 1) f⁻¹ x :=
    ((contMDiff_inv (𝓡 1) 1).mdifferentiableAt one_ne_zero).comp x hf
  have h := mpullback_mul_circleAngularForm_apply hf hinv
  have h1 : f * f⁻¹ = fun _ ↦ (1 : Circle) := funext fun y ↦ mul_inv_cancel (f y)
  rw [h1, mpullback_const_circleAngularForm, Pi.zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- For a differentiable map `f : M → Circle`, `(f⁻¹)^* dθ = - f^* dθ`. -/
theorem mpullback_inv_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f) :
    mpullback I (𝓡 1) f⁻¹ circleAngularForm = -mpullback I (𝓡 1) f circleAngularForm :=
  funext fun x ↦ mpullback_inv_circleAngularForm_apply (hf x)

/-- For a differentiable map `f : M → Circle`, `(fun y ↦ (f y)⁻¹)^* dθ = - f^* dθ`. -/
theorem mpullback_fun_inv_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f) :
    mpullback I (𝓡 1) (fun y ↦ (f y)⁻¹) circleAngularForm =
      -mpullback I (𝓡 1) f circleAngularForm :=
  mpullback_inv_circleAngularForm hf

/-- If `f, g : M → Circle` are differentiable at `x`, then `(f / g)^* dθ = f^* dθ - g^* dθ` at `x`.
-/
@[to_fun mpullback_fun_div_circleAngularForm_apply]
theorem mpullback_div_circleAngularForm_apply {f g : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (hg : MDifferentiableAt I (𝓡 1) g x) :
    mpullback I (𝓡 1) (f / g) circleAngularForm x =
      mpullback I (𝓡 1) f circleAngularForm x - mpullback I (𝓡 1) g circleAngularForm x := by
  have hinv : MDifferentiableAt I (𝓡 1) g⁻¹ x :=
    ((contMDiff_inv (𝓡 1) 1).mdifferentiableAt one_ne_zero).comp x hg
  rw [div_eq_mul_inv, mpullback_mul_circleAngularForm_apply hf hinv,
    mpullback_inv_circleAngularForm_apply hg, sub_eq_add_neg]

/-- For differentiable maps `f, g : M → Circle`, `(f / g)^* dθ = f^* dθ - g^* dθ`. -/
theorem mpullback_div_circleAngularForm {f g : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (hg : MDifferentiable I (𝓡 1) g) :
    mpullback I (𝓡 1) (f / g) circleAngularForm =
      mpullback I (𝓡 1) f circleAngularForm - mpullback I (𝓡 1) g circleAngularForm :=
  funext fun x ↦ mpullback_div_circleAngularForm_apply (hf x) (hg x)

/-- For differentiable maps `f, g : M → Circle`, `(fun y ↦ f y / g y)^* dθ = f^* dθ - g^* dθ`. -/
theorem mpullback_fun_div_circleAngularForm {f g : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (hg : MDifferentiable I (𝓡 1) g) :
    mpullback I (𝓡 1) (fun y ↦ f y / g y) circleAngularForm =
      mpullback I (𝓡 1) f circleAngularForm - mpullback I (𝓡 1) g circleAngularForm :=
  mpullback_div_circleAngularForm hf hg

/-- If `f : M → Circle` is differentiable at `x`, then `(f ^ n)^* dθ = n • f^* dθ` at `x` for every
`n : ℕ`. -/
@[to_fun mpullback_fun_pow_circleAngularForm_apply]
theorem mpullback_pow_circleAngularForm_apply {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (n : ℕ) :
    mpullback I (𝓡 1) (f ^ n) circleAngularForm x =
      (n : ℝ) • mpullback I (𝓡 1) f circleAngularForm x := by
  induction n with
  | zero =>
    have h1 : (f ^ 0 : M → Circle) = fun _ ↦ (1 : Circle) := funext fun _ ↦ pow_zero _
    rw [h1, mpullback_const_circleAngularForm]
    simp
  | succ n ih =>
    have hpow : MDifferentiableAt I (𝓡 1) (f ^ n) x :=
      (((contMDiff_pow n : ContMDiff (𝓡 1) (𝓡 1) 1 _)).mdifferentiableAt one_ne_zero).comp x hf
    rw [pow_succ, mpullback_mul_circleAngularForm_apply hpow hf, ih, Nat.cast_add, Nat.cast_one,
      add_smul, one_smul]

/-- For a differentiable map `f : M → Circle` and `n : ℕ`, `(f ^ n)^* dθ = n • f^* dθ`. -/
theorem mpullback_pow_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (n : ℕ) :
    mpullback I (𝓡 1) (f ^ n) circleAngularForm =
      (n : ℝ) • mpullback I (𝓡 1) f circleAngularForm :=
  funext fun x ↦ mpullback_pow_circleAngularForm_apply (hf x) n

/-- For a differentiable map `f : M → Circle` and `n : ℕ`,
`(fun y ↦ f y ^ n)^* dθ = n • f^* dθ`. -/
theorem mpullback_fun_pow_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (n : ℕ) :
    mpullback I (𝓡 1) (fun y ↦ f y ^ n) circleAngularForm =
      (n : ℝ) • mpullback I (𝓡 1) f circleAngularForm :=
  mpullback_pow_circleAngularForm hf n

/-- If `f : M → Circle` is differentiable at `x`, then `(f ^ k)^* dθ = k • f^* dθ` at `x` for every
`k : ℤ`. -/
@[to_fun mpullback_fun_zpow_circleAngularForm_apply]
theorem mpullback_zpow_circleAngularForm_apply {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (k : ℤ) :
    mpullback I (𝓡 1) (f ^ k) circleAngularForm x =
      (k : ℝ) • mpullback I (𝓡 1) f circleAngularForm x := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [zpow_natCast, Int.cast_natCast] using mpullback_pow_circleAngularForm_apply hf n
  · have hpow : MDifferentiableAt I (𝓡 1) (f ^ n) x :=
      (((contMDiff_pow n : ContMDiff (𝓡 1) (𝓡 1) 1 _)).mdifferentiableAt one_ne_zero).comp x hf
    simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast]
    rw [mpullback_inv_circleAngularForm_apply hpow, mpullback_pow_circleAngularForm_apply hf n]
    ext v
    simp

/-- For a differentiable map `f : M → Circle` and `k : ℤ`, `(f ^ k)^* dθ = k • f^* dθ`. -/
theorem mpullback_zpow_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (k : ℤ) :
    mpullback I (𝓡 1) (f ^ k) circleAngularForm =
      (k : ℝ) • mpullback I (𝓡 1) f circleAngularForm :=
  funext fun x ↦ mpullback_zpow_circleAngularForm_apply (hf x) k

/-- For a differentiable map `f : M → Circle` and `k : ℤ`,
`(fun y ↦ f y ^ k)^* dθ = k • f^* dθ`. -/
theorem mpullback_fun_zpow_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (k : ℤ) :
    mpullback I (𝓡 1) (fun y ↦ f y ^ k) circleAngularForm =
      (k : ℝ) • mpullback I (𝓡 1) f circleAngularForm :=
  mpullback_zpow_circleAngularForm hf k

/-- If `f : M → Circle` is differentiable at `x`, then `(-f)^* dθ = f^* dθ` at `x`. -/
@[to_fun mpullback_fun_neg_circleAngularForm_apply]
theorem mpullback_neg_circleAngularForm_apply {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) :
    mpullback I (𝓡 1) (-f) circleAngularForm x = mpullback I (𝓡 1) f circleAngularForm x := by
  have hneg : -f = (fun _ : M ↦ (-1 : Circle)) * f := funext fun y ↦ (neg_one_mul (f y)).symm
  rw [hneg, mpullback_mul_circleAngularForm_apply mdifferentiableAt_const hf,
    mpullback_const_circleAngularForm, Pi.zero_apply, zero_add]

/-- For a differentiable map `f : M → Circle`, `(-f)^* dθ = f^* dθ`. -/
theorem mpullback_neg_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f) :
    mpullback I (𝓡 1) (-f) circleAngularForm = mpullback I (𝓡 1) f circleAngularForm :=
  funext fun x ↦ mpullback_neg_circleAngularForm_apply (hf x)

/-- For a differentiable map `f : M → Circle`, `(fun y ↦ -f y)^* dθ = f^* dθ`. -/
theorem mpullback_fun_neg_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f) :
    mpullback I (𝓡 1) (fun y ↦ -f y) circleAngularForm = mpullback I (𝓡 1) f circleAngularForm :=
  mpullback_neg_circleAngularForm hf

end PullbackAngularForm

/-- Left multiplication on `Circle` preserves the angular form `dθ`. -/
@[simp]
theorem mpullback_mul_left_circleAngularForm (z₀ : Circle) :
    mpullback (𝓡 1) (𝓡 1) (z₀ * ·) circleAngularForm = circleAngularForm := by
  simpa only [id_eq, mpullback_const_circleAngularForm, zero_add, mpullback_id] using
    mpullback_fun_mul_circleAngularForm (I := 𝓡 1) (mdifferentiable_const (c := z₀))
      mdifferentiable_id

/-- Right multiplication on `Circle` preserves the angular form `dθ`. -/
@[simp]
theorem mpullback_mul_right_circleAngularForm (z₀ : Circle) :
    mpullback (𝓡 1) (𝓡 1) (· * z₀) circleAngularForm = circleAngularForm := by
  simpa only [id_eq, mpullback_const_circleAngularForm, add_zero, mpullback_id] using
    mpullback_fun_mul_circleAngularForm (I := 𝓡 1) mdifferentiable_id
      (mdifferentiable_const (c := z₀))

/-- Inversion on `Circle` negates the angular form `dθ`. -/
@[simp]
theorem mpullback_inv_id_circleAngularForm :
    mpullback (𝓡 1) (𝓡 1) (·⁻¹ : Circle → Circle) circleAngularForm = -circleAngularForm := by
  simpa only [id_eq, mpullback_id] using mpullback_fun_inv_circleAngularForm (I := 𝓡 1)
    mdifferentiable_id

/-- The natural power map `z ↦ z ^ n` on `Circle` pulls `dθ` back to `n • dθ`. -/
@[simp]
theorem mpullback_pow_id_circleAngularForm (n : ℕ) :
    mpullback (𝓡 1) (𝓡 1) (fun z : Circle ↦ z ^ n) circleAngularForm =
      (n : ℝ) • circleAngularForm := by
  simpa only [id_eq, mpullback_id] using mpullback_fun_pow_circleAngularForm (I := 𝓡 1)
    mdifferentiable_id n

/-- **Pullback of `dθ` by `z ↦ z ^ k`.** For every integer `k : ℤ`, the power map `z ↦ z ^ k` on
`Circle` pulls the angular form `dθ` back to `k • dθ`. -/
@[simp]
theorem mpullback_zpow_id_circleAngularForm (k : ℤ) :
    mpullback (𝓡 1) (𝓡 1) (fun z : Circle ↦ z ^ k) circleAngularForm =
      (k : ℝ) • circleAngularForm := by
  simpa only [id_eq, mpullback_id] using mpullback_fun_zpow_circleAngularForm (I := 𝓡 1)
    mdifferentiable_id k

/-- Negation `z ↦ -z` on `Circle` preserves the angular form `dθ`. -/
@[simp]
theorem mpullback_neg_id_circleAngularForm :
    mpullback (𝓡 1) (𝓡 1) (fun z : Circle ↦ -z) circleAngularForm = circleAngularForm := by
  simpa only [id_eq, mpullback_id] using mpullback_fun_neg_circleAngularForm (I := 𝓡 1)
    mdifferentiable_id

end TauCeti

/-! ### The angular form on the circles `AddCircle p` -/

namespace AddCircle

open TauCeti TauCeti.Manifold.Orientation
open scoped Real

variable (p : ℝ) [Fact (0 < p)]

/-- **The angular form in the time coordinate.** The identification
`toCircle : AddCircle p → Circle`, `[t] ↦ exp (2π i t / p)`, pulls the angular form `dθ` of the
unit circle back to `(2π / p) • dt_p`, where `dt_p` is the time form of `AddCircle p`. Equivalently
the angle is `θ = 2π t / p`, and `dt_p = (p / 2π) dθ`; for the unit period, `dt = dθ / 2π`. -/
@[simp]
theorem mpullback_toCircle_circleAngularForm :
    mpullback 𝓘(ℝ) (𝓡 1) (toCircle : AddCircle p → Circle) circleAngularForm =
      (2 * π / p) • (timeForm p).val := by
  set c : ℝ := 2 * π / p
  refine mpullback_coe_injective p ?_
  have hmul : MDifferentiable 𝓘(ℝ) 𝓘(ℝ) fun t : ℝ ↦ c * t :=
    (contDiff_const.mul contDiff_id).contMDiff.mdifferentiable one_ne_zero
  -- Read on `ℝ`, `toCircle` is `Circle.exp` after multiplication by `c`, which pulls `dθ` back to
  -- `dt` and then to `c • dt`.
  have hcomp : (toCircle : AddCircle p → Circle) ∘ ((↑) : ℝ → AddCircle p) =
      Circle.exp ∘ fun t : ℝ ↦ c * t :=
    funext toCircle_apply_mk
  rw [mpullback_smul, mpullback_coe_timeForm,
    ← mpullback_comp ((contMDiff_coe p 1).mdifferentiable one_ne_zero)
      ((contMDiff_toCircle p 1).mdifferentiable one_ne_zero), hcomp,
    mpullback_comp hmul (contMDiff_circleExp.mdifferentiable one_ne_zero),
    mpullback_circleExp_circleAngularForm]
  funext t
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [mpullback_apply, ((hasFDerivAt_id t).const_mul c).hasMFDerivAt.mfderiv, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, mextDeriv_ofFunction_id_apply,
    mextDeriv_ofFunction_id_apply]
  -- Tangent vectors of `ℝ` are real numbers, on which `c • id` acts by multiplication by `c`.
  rfl

/-- The identification `toCircle : AddCircle p → Circle` preserves orientation, from the positive
orientation of `AddCircle p`, on which `dt_p` is positive, to the counterclockwise orientation of
the unit circle, on which `dθ` is positive. -/
theorem isOrientationPreservingAt_toCircle (x : AddCircle p) :
    IsOrientationPreservingAt (AddCircle.orientation p) circleOrientation
      (toCircle : AddCircle p → Circle) x := by
  rw [← coe_diffeomorphCircle p 1]
  let e := (diffeomorphCircle p 1).mfderivToContinuousLinearEquiv one_ne_zero x
  let b : Module.Basis (Fin 1) ℝ (TangentSpace 𝓘(ℝ) x) := Module.Basis.singleton (Fin 1) ℝ
  have hb (i : Fin 1) :
      mfderiv 𝓘(ℝ) (𝓡 1) (diffeomorphCircle p 1) x (b i) = b.map e.toLinearEquiv i := by
    rw [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact (DFunLike.congr_fun
      ((diffeomorphCircle p 1).mfderivToContinuousLinearEquiv_coe one_ne_zero (x := x)) (b i)).symm
  -- The basis `1` is positive for the orientation of `AddCircle p`, and its image is positive for
  -- the counterclockwise orientation because `dθ` takes the positive value `2π / p` on it.
  refine (isOrientationPreservingAt_iff_of_basis b _ hb).mpr
    (iff_of_true (orientationAt_orientation p x).symm ?_)
  rw [orientation_eq_orientationAt_circleOrientation_iff, ← funext hb, ← mpullback_apply,
    coe_diffeomorphCircle, mpullback_toCircle_circleAngularForm]
  -- The time form takes the value `1` on the basis vector `1`.
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, timeForm_apply]
  exact mul_pos (div_pos Real.two_pi_pos (Fact.out : 0 < p))
    (one_pos.trans_eq (Module.Basis.singleton_apply (Fin 1) ℝ 0).symm)

/-- **The time form on the unit circle.** Transported to the unit circle by the identification
`AddCircle p ≃ Circle`, the time form `dt_p` is `(p / 2π) dθ`. -/
theorem mpullback_homeomorphCircle_symm_timeForm :
    mpullback (𝓡 1) 𝓘(ℝ) (homeomorphCircle (Fact.out : 0 < p).ne').symm (timeForm p).val =
      (p / (2 * π)) • circleAngularForm := by
  have hc : p / (2 * π) * (2 * π / p) = 1 := by
    field_simp [(Fact.out : 0 < p).ne', Real.two_pi_pos.ne']
  have ht : (timeForm p).val =
      (p / (2 * π)) • mpullback 𝓘(ℝ) (𝓡 1) (toCircle : AddCircle p → Circle) circleAngularForm := by
    rw [mpullback_toCircle_circleAngularForm, smul_smul, hc, one_smul]
  -- The inverse homeomorphism is the inverse of the diffeomorphism `toCircle`.
  rw [ht, mpullback_smul, ← coe_diffeomorphCircle p ω, ← coe_diffeomorphCircle_symm p ω,
    mpullback_symm_mpullback (by simp)]

end AddCircle
