/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
import TauCeti.Geometry.Manifold.Riemannian.Sphere.StereographicArea

/-!
# The area of the unit two-sphere

For an orientation `o` of `ℝ³ = EuclideanSpace ℝ (Fin 3)`, the outward-normal top form
`o.sphereVolumeForm` of the unit sphere `S²` sends two tangent vectors `a, b` at `u` to
`vol(u, a, b)`. For the standard orientation this is the triple product
`u ⬝ᵥ (a ⨯₃ b)` (`EuclideanSpace.volumeForm_basisFun_orientation_three`), the area form of the
round sphere. This file proves that its integral over `S²` with the outward-normal orientation is
the area `4π` of the unit sphere (`Orientation.integralTopForm_sphereOrientation_sphereVolumeForm`),
for either orientation of `ℝ³`.

The integral is computed through inverse stereographic projection from the south pole,

`q(x, y) = (2x, 2y, 1 - x² - y²) / (1 + x² + y²)`

(`TauCeti.stereoSphere`), a smooth injective parametrization of the sphere minus the south pole
which pulls the area form back to `4 / (1 + x² + y²)² dx ∧ dy`
(`TauCeti.sphereVolumeForm_mfderiv_stereoSphere_apply`). This density is positive, so `q` is
positively oriented for the outward normal, and the integral of the area form is the integral of
this density over the plane. The density is `4π` times the Fubini–Study density,
whose total integral is one (`OnePoint.integral_fubiniStudyDensity`).

## Main results

* `Orientation.integralTopForm_sphereOrientation_sphereVolumeForm`: the outward-normal area form
  of the unit sphere of `ℝ³` integrates to `4π`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (the outward-normal orientation and the Riemannian volume form of a
  hypersurface) and Chapter 16 (integration over parametrizations).
-/

public section

noncomputable section

open Metric Module MeasureTheory Matrix
open scoped Manifold ContDiff

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-! ### Orientation of the stereographic parametrization -/

/-- On the images of the standard basis vectors under the derivative of inverse stereographic
projection, the area form is the density `4 / (1 + x² + y²)²`. -/
private theorem sphereVolumeForm_mfderiv_stereoSphere_basisFun (z : ℝ²) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val (stereoSphere z)
      (fun i ↦ mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i)) =
        4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 := by
  have h : (fun i ↦ mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
      ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i)) =
        ![mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z (EuclideanSpace.single 0 1),
          mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z (EuclideanSpace.single 1 1)] :=
    funext fun i ↦ by fin_cases i <;> simp [EuclideanSpace.basisFun_apply]
  rw [h, sphereVolumeForm_mfderiv_stereoSphere_apply]
  simp


private theorem injective_mfderiv_stereoSphere (z : ℝ²) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z) := by
  set L := mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
  -- The area form does not vanish on the images of the basis vectors, so they are independent.
  have hli : LinearIndependent ℝ fun i ↦ L ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) := by
    by_contra h
    have h0 := ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val
      (stereoSphere z)).toAlternatingMap.map_linearDependent _ h
    rw [ContinuousAlternatingMap.coe_toAlternatingMap,
      sphereVolumeForm_mfderiv_stereoSphere_basisFun] at h0
    have : (0 : ℝ) < 4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 := by positivity
    exact this.ne' h0
  exact LinearMap.injective_of_linearIndependent (f := L.toLinearMap)
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.span_eq hli

/-- The derivative of the parametrization as an isomorphism onto the tangent space. -/
private def stereoDerivEquiv (z : ℝ²) : ℝ² ≃L[ℝ] TangentSpace (𝓡 2) (stereoSphere z) :=
  (LinearEquiv.ofInjectiveEndo (mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z : ℝ² →L[ℝ] ℝ²).toLinearMap
    (injective_mfderiv_stereoSphere z)).toContinuousLinearEquiv

private theorem stereoDerivEquiv_apply (z v : ℝ²) :
    stereoDerivEquiv z v = mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z v :=
  -- Both `toContinuousLinearEquiv` and `ofInjectiveEndo` keep the underlying function.
  rfl

private theorem hasMFDerivAt_stereoSphere (z : ℝ²) :
    HasMFDerivAt 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
      ((stereoDerivEquiv z).toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace z).toContinuousLinearMap) := by
  have heq : (stereoDerivEquiv z).toContinuousLinearMap.comp
      (NormedSpace.fromTangentSpace z).toContinuousLinearMap =
        mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z := by
    ext v
    exact stereoDerivEquiv_apply z v
  rw [heq]
  exact ((contMDiff_stereoSphere z).mdifferentiableAt (by simp)).hasMFDerivAt

/-- The parametrization is positively oriented for the outward-normal orientation. -/
private theorem map_stereoDerivEquiv_orientation (z : ℝ²) :
    Orientation.map (Fin 2) (stereoDerivEquiv z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation.orientationAt
        (stereoSphere z) := by
  rw [← Module.Basis.orientation_map,
    Orientation.orientation_eq_orientationAt_sphereOrientation_iff,
    ← Orientation.sphereVolumeForm_apply]
  have hmap : ⇑((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.map
      (stereoDerivEquiv z).toLinearEquiv) = fun i ↦ mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) := by
    funext i
    rw [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv, stereoDerivEquiv_apply]
  rw [hmap, sphereVolumeForm_mfderiv_stereoSphere_basisFun]
  positivity


/-! ### The area -/

/-- The area density `4 / (1 + x² + y²)²` integrates to `4π` over the plane: it is `4π` times
the Fubini–Study density. -/
private theorem integral_stereoDensity :
    ∫ z : ℝ², 4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 = 4 * Real.pi := by
  have hn (z : ℝ²) : 1 + z 0 ^ 2 + z 1 ^ 2 = 1 + ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, add_assoc]
  simp_rw [hn]
  rw [← integral_comp Complex.orthonormalBasisOneI.repr (fun y : ℝ² ↦ 4 / (1 + ‖y‖ ^ 2) ^ 2)]
  simp only [LinearIsometryEquiv.norm_map]
  have h (w : ℂ) : 4 / (1 + ‖w‖ ^ 2) ^ 2 = 4 * Real.pi * OnePoint.fubiniStudyDensity w := by
    rw [OnePoint.fubiniStudyDensity_def]
    field_simp
  simp_rw [h]
  rw [integral_const_mul, OnePoint.integral_fubiniStudyDensity, mul_one]

/-- The outward-normal area form of the standard orientation integrates to `4π`. -/
private theorem integralTopForm_sphereVolumeForm_basisFun :
    integralTopForm (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val =
        4 * Real.pi := by
  obtain ⟨l, hl⟩ :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation.exists_lift
  have hc : IsCompact (_root_.tsupport (α := ℝ² [⋀^Fin 2]→L[ℝ] ℝ)
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val) :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have h := integralTopForm_eq_oriented_parametrization l
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val
    (IsSmoothForm.integrableTopForm
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.isSmoothForm hc
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
    MeasurableSet.univ (Set.countable_singleton sphereSouthPole).isNullSet
    (by rw [Set.image_univ, range_stereoSphere]) injective_stereoSphere.injOn stereoDerivEquiv
    (fun z _ ↦ hasMFDerivAt_stereoSphere z)
    (fun z _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl, map_stereoDerivEquiv_orientation])
  rw [OrthonormalBasis.addHaar_eq_volume] at h
  rw [← hl, h.2, Measure.restrict_univ]
  simp_rw [stereoDerivEquiv_apply, sphereVolumeForm_mfderiv_stereoSphere_basisFun]
  exact integral_stereoDensity

end TauCeti

/-- **The area of the unit sphere is `4π`.** For either orientation `o` of `ℝ³`, the
outward-normal area form `(a, b) ↦ vol(u, a, b)` of the unit sphere integrates to `4π` over the
sphere with its outward-normal orientation. -/
theorem Orientation.integralTopForm_sphereOrientation_sphereVolumeForm
    (o : Orientation ℝ ℝ³ (Fin 3)) :
    TauCeti.integralTopForm o.sphereOrientation o.sphereVolumeForm.val = 4 * Real.pi := by
  rcases o.eq_or_eq_neg (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation (by simp)
    with rfl | rfl
  · exact TauCeti.integralTopForm_sphereVolumeForm_basisFun
  · -- Reversing `o` reverses both the orientation of the sphere and the sign of the form.
    rw [Orientation.sphereOrientation_neg, Orientation.sphereVolumeForm_neg, Submodule.coe_neg,
      ← neg_one_smul ℝ, TauCeti.integralTopForm_neg, TauCeti.integralTopForm_smul,
      TauCeti.integralTopForm_sphereVolumeForm_basisFun]
    ring
