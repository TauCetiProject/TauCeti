/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic

/-!
# The area of the unit two-sphere

For an orientation `o` of `ℝ³ = EuclideanSpace ℝ (Fin 3)`, the outward-normal top form
`o.sphereTopForm` of the unit sphere `S²` sends two tangent vectors `a, b` at `u` to
`vol(u, a, b)`. For the standard orientation this is the triple product
`u ⬝ᵥ (a ⨯₃ b)` (`EuclideanSpace.volumeForm_eq_dotProduct_cross`), the area form of the round
sphere. This file proves that its integral over `S²` with the outward-normal orientation is the
area `4π` of the unit sphere (`Orientation.integralTopForm_sphereOrientation_sphereTopForm`), for
either orientation of `ℝ³`.

The integral is computed through inverse stereographic projection from the south pole,

`q(x, y) = (2x, 2y, 1 - x² - y²) / (1 + x² + y²)`,

Mathlib's `stereoInvFunAux` from `(0, 0, -1)` read on the equatorial plane through
`(x, y) ↦ (2x, 2y, 0)`. It is a smooth injective parametrization of the sphere minus the south
pole. Its derivative is given by `TauCeti.fderiv_stereoInvFunAux_apply`, and in coordinates the
triple product of `q` with its two partial derivatives is `4 / (1 + x² + y²)²`. This is positive,
so `q` is positively oriented for the outward normal, and the integral of the area form is the
integral of this density over the plane. The density is `4π` times the Fubini–Study density,
whose total integral is one (`OnePoint.integral_fubiniStudyDensity`).

## Main results

* `EuclideanSpace.volumeForm_eq_dotProduct_cross`: the volume form of the standard orientation of
  `ℝ³` is the triple product.
* `Orientation.integralTopForm_sphereOrientation_sphereTopForm`: the outward-normal area form of
  the unit sphere of `ℝ³` integrates to `4π`.

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

/-- **The volume form of `ℝ³` is the triple product.** For the standard orientation of
`EuclideanSpace ℝ (Fin 3)`, `vol(u, a, b) = u ⬝ᵥ (a ⨯₃ b)`. -/
theorem EuclideanSpace.volumeForm_eq_dotProduct_cross (u a b : ℝ³) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.volumeForm ![u, a, b] =
      u.ofLp ⬝ᵥ a.ofLp ⨯₃ b.ofLp := by
  rw [Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 3) ℝ) rfl,
    Module.Basis.det_apply, Matrix.det_fin_three]
  simp [Module.Basis.toMatrix_apply, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

namespace TauCeti

/-! ### Inverse stereographic projection from the south pole -/

/-- The coordinates `(2x, 2y, 1 - x² - y²) / (1 + x² + y²)` of inverse stereographic projection
from the south pole. -/
private def stereoVec (x y : ℝ) : Fin 3 → ℝ :=
  ![2 * x / (1 + x ^ 2 + y ^ 2), 2 * y / (1 + x ^ 2 + y ^ 2),
    (1 - x ^ 2 - y ^ 2) / (1 + x ^ 2 + y ^ 2)]

/-- The south pole `(0, 0, -1)` of the unit sphere, as a vector of `ℝ³`. -/
private def southPoleVec : ℝ³ :=
  WithLp.toLp 2 ![0, 0, -1]

private theorem norm_southPoleVec : ‖southPoleVec‖ = 1 := by
  rw [southPoleVec, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [Fin.sum_univ_three]

/-- The linear map `z ↦ (2 z₀, 2 z₁, 0)` onto the plane orthogonal to the south pole. -/
private def planeEmbed : ℝ² →L[ℝ] ℝ³ :=
  LinearMap.toContinuousLinearMap
    { toFun z := WithLp.toLp 2 ![2 * z 0, 2 * z 1, 0]
      map_add' z w := by ext i; fin_cases i <;> simp [mul_add]
      map_smul' c z := by ext i; fin_cases i <;> simp [mul_left_comm] }

private theorem planeEmbed_apply (z : ℝ²) :
    planeEmbed z = WithLp.toLp 2 ![2 * z 0, 2 * z 1, 0] :=
  (rfl)

private theorem norm_planeEmbed_sq (z : ℝ²) : ‖planeEmbed z‖ ^ 2 = 4 * (z 0 ^ 2 + z 1 ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [planeEmbed_apply, Fin.sum_univ_three]
  ring

/-- Inverse stereographic projection from the south pole, as a map `ℝ² → ℝ³`: Mathlib's
`stereoInvFunAux` from the south pole, after the identification `z ↦ (2 z₀, 2 z₁, 0)` of `ℝ²` with
the equatorial plane. -/
private def stereoParam (z : ℝ²) : ℝ³ :=
  stereoInvFunAux southPoleVec (planeEmbed z)

/-- In coordinates, `stereoParam z = (2x, 2y, 1 - x² - y²) / (1 + x² + y²)`. -/
private theorem stereoParam_eq (z : ℝ²) :
    stereoParam z = WithLp.toLp 2 (stereoVec (z 0) (z 1)) := by
  have hs : 1 + z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by positivity
  rw [stereoParam, stereoInvFunAux_apply, norm_planeEmbed_sq]
  ext i
  fin_cases i <;>
  · simp [planeEmbed_apply, southPoleVec, stereoVec]
    field_simp
    ring

private theorem stereoParam_mem_sphere (z : ℝ²) : stereoParam z ∈ S² := by
  refine stereoInvFunAux_mem norm_southPoleVec ?_
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [planeEmbed_apply, southPoleVec, dotProduct, Fin.sum_univ_three]

private theorem contDiff_stereoParam : ContDiff ℝ ∞ stereoParam :=
  contDiff_stereoInvFunAux.comp planeEmbed.contDiff

private theorem fderiv_stereoParam_apply (z a : ℝ²) :
    fderiv ℝ stereoParam z a =
      fderiv ℝ (stereoInvFunAux southPoleVec) (planeEmbed z) (planeEmbed a) := by
  have h := ((contDiff_stereoInvFunAux (v := southPoleVec) (m := 1)).differentiable
    one_ne_zero _).hasFDerivAt.comp z planeEmbed.hasFDerivAt
  rw [show stereoParam = stereoInvFunAux southPoleVec ∘ planeEmbed from rfl, h.fderiv]
  rfl

/-- The triple product of the parametrization with its two partial derivatives is the area
density `4 / (1 + x² + y²)²`. -/
private theorem dotProduct_cross_fderiv_stereoParam (z : ℝ²) :
    (stereoParam z).ofLp ⬝ᵥ (fderiv ℝ stereoParam z (EuclideanSpace.single 0 1)).ofLp ⨯₃
      (fderiv ℝ stereoParam z (EuclideanSpace.single 1 1)).ofLp =
        4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 := by
  have hs : 1 + z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by positivity
  rw [fderiv_stereoParam_apply, fderiv_stereoParam_apply, fderiv_stereoInvFunAux_apply,
    fderiv_stereoInvFunAux_apply, norm_planeEmbed_sq, stereoParam_eq]
  simp [stereoVec, cross_apply, dotProduct, Fin.sum_univ_three, planeEmbed_apply, southPoleVec,
    PiLp.inner_apply]
  field_simp
  ring

/-- Inverse stereographic projection from the south pole, as a map into the unit sphere. -/
private def stereoSphere : ℝ² → S² :=
  Set.codRestrict stereoParam _ stereoParam_mem_sphere

private theorem contMDiff_stereoSphere : ContMDiff 𝓘(ℝ, ℝ²) (𝓡 2) ∞ stereoSphere :=
  contDiff_stereoParam.contMDiff.codRestrict_sphere stereoParam_mem_sphere

private theorem mvfderiv_coe_mfderiv_stereoSphere (z : ℝ²) (v : TangentSpace 𝓘(ℝ, ℝ²) z) :
    mvfderiv (𝓡 2) ((↑) : S² → ℝ³) (stereoSphere z)
      (mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z v) = fderiv ℝ stereoParam z v :=
  (mvfderiv_comp_apply z
    ((contMDiff_coe_sphere (n := 2) (m := 1) _).mdifferentiableAt one_ne_zero)
    ((contMDiff_stereoSphere z).mdifferentiableAt (by simp)) v).symm.trans
      (mvfderiv_eq_fderiv_apply stereoParam z v)

/-- On the derivatives of the parametrization, the area form is the density
`4 / (1 + x² + y²)²`. -/
private theorem sphereTopForm_mfderiv_stereoSphere (z : ℝ²) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereTopForm (stereoSphere z)
      (fun i ↦ mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i)) =
        4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 := by
  rw [Orientation.sphereTopForm_apply, ← dotProduct_cross_fderiv_stereoParam,
    ← EuclideanSpace.volumeForm_eq_dotProduct_cross]
  refine congrArg _ (funext fun i ↦ ?_)
  fin_cases i
  · rfl
  · exact (mvfderiv_coe_mfderiv_stereoSphere z _).trans
      (by simp [EuclideanSpace.basisFun_apply])
  · exact (mvfderiv_coe_mfderiv_stereoSphere z _).trans
      (by simp [EuclideanSpace.basisFun_apply])

private theorem injective_mfderiv_stereoSphere (z : ℝ²) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z) := by
  set L := mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
  -- The area form does not vanish on the images of the basis vectors, so they are independent.
  have hli : LinearIndependent ℝ fun i ↦ L ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) := by
    by_contra h
    have h0 := ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereTopForm
      (stereoSphere z)).toAlternatingMap.map_linearDependent _ h
    rw [ContinuousAlternatingMap.coe_toAlternatingMap, sphereTopForm_mfderiv_stereoSphere] at h0
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
    ← Orientation.sphereTopForm_apply]
  have hmap : ⇑((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.map
      (stereoDerivEquiv z).toLinearEquiv) = fun i ↦ mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) := by
    funext i
    rw [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv, stereoDerivEquiv_apply]
  rw [hmap, sphereTopForm_mfderiv_stereoSphere]
  positivity

/-! ### The image of the parametrization -/

private theorem one_add_stereoParam_apply_two (z : ℝ²) :
    1 + stereoParam z 2 = 2 / (1 + z 0 ^ 2 + z 1 ^ 2) := by
  have hs : 1 + z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by positivity
  simp only [stereoParam_eq, stereoVec, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  field_simp
  ring

/-- Stereographic projection from the south pole inverts the parametrization:
`zᵢ = qᵢ(z) / (1 + q₂(z))`. -/
private theorem stereoParam_apply_div (z : ℝ²) (i : Fin 2) :
    stereoParam z (Fin.castSucc i) / (1 + stereoParam z 2) = z i := by
  have hs : 1 + z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by positivity
  rw [one_add_stereoParam_apply_two]
  fin_cases i <;>
  · simp [stereoParam_eq, stereoVec]
    field_simp

private theorem injective_stereoSphere : Function.Injective stereoSphere := by
  intro z w h
  have h' : stereoParam z = stereoParam w := congrArg Subtype.val h
  ext i
  rw [← stereoParam_apply_div z i, ← stereoParam_apply_div w i, h']

/-- The south pole `(0, 0, -1)` of the unit sphere. -/
private def southPole : S² :=
  ⟨southPoleVec, mem_sphere_zero_iff_norm.2 norm_southPoleVec⟩

private theorem sq_add_sq_add_sq_of_mem_sphere (u : S²) :
    u.1 0 ^ 2 + u.1 1 ^ 2 + u.1 2 ^ 2 = 1 := by
  have h := u.2
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  simpa [Fin.sum_univ_three] using h

/-- The parametrization covers exactly the sphere minus the south pole. -/
private theorem range_stereoSphere : Set.range stereoSphere = {southPole}ᶜ := by
  ext u
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, rfl⟩ h
    -- The last coordinate `(1 - x² - y²) / (1 + x² + y²)` is never `-1`.
    have hs : (0 : ℝ) < 1 + z 0 ^ 2 + z 1 ^ 2 := by positivity
    have h2 : (1 - z 0 ^ 2 - z 1 ^ 2) / (1 + z 0 ^ 2 + z 1 ^ 2) = -1 := by
      simpa [stereoSphere, stereoParam_eq, stereoVec, southPole, southPoleVec] using
        congrArg (fun v : S² ↦ (v : ℝ³) 2) h
    rw [div_eq_iff hs.ne'] at h2
    linarith
  · intro hu
    have hsq := sq_add_sq_add_sq_of_mem_sphere u
    have h2 : 1 + u.1 2 ≠ 0 := by
      intro h2
      apply hu
      have hu2 : u.1 2 = -1 := by linarith
      have h01 : u.1 0 ^ 2 + u.1 1 ^ 2 = 0 := by rw [hu2] at hsq; linarith
      have h0 : u.1 0 = 0 := by nlinarith [sq_nonneg (u.1 0), sq_nonneg (u.1 1)]
      have h1 : u.1 1 = 0 := by nlinarith [sq_nonneg (u.1 0), sq_nonneg (u.1 1)]
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [southPole, southPoleVec, h0, h1, hu2]
    -- The preimage is the stereographic projection `(u₀, u₁) / (1 + u₂)` of `u`.
    refine ⟨WithLp.toLp 2 ![u.1 0 / (1 + u.1 2), u.1 1 / (1 + u.1 2)], ?_⟩
    apply Subtype.ext
    ext i
    fin_cases i
    · simp [stereoSphere, stereoParam_eq, stereoVec]
      field_simp
      linear_combination (-u.1 0) * hsq
    · simp [stereoSphere, stereoParam_eq, stereoVec]
      field_simp
      linear_combination (-u.1 1) * hsq
    · simp [stereoSphere, stereoParam_eq, stereoVec]
      field_simp
      linear_combination (-1 - u.1 2) * hsq

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
private theorem integralTopForm_sphereTopForm_basisFun :
    integralTopForm (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereTopForm = 4 * Real.pi := by
  obtain ⟨l, hl⟩ :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation.exists_lift
  have hc : IsCompact (_root_.tsupport (α := ℝ² [⋀^Fin 2]→L[ℝ] ℝ)
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereTopForm) :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have h := integralTopForm_eq_oriented_parametrization l
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereTopForm
    (IsSmoothForm.integrableTopForm
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.isSmoothForm_sphereTopForm hc
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
    MeasurableSet.univ (Set.finite_singleton southPole)
    (by rw [Set.image_univ, range_stereoSphere]) injective_stereoSphere.injOn stereoDerivEquiv
    (fun z _ ↦ hasMFDerivAt_stereoSphere z)
    (fun z _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl, map_stereoDerivEquiv_orientation])
  rw [OrthonormalBasis.addHaar_eq_volume] at h
  rw [← hl, h.2, Measure.restrict_univ]
  simp_rw [stereoDerivEquiv_apply, sphereTopForm_mfderiv_stereoSphere]
  exact integral_stereoDensity

end TauCeti

/-- **The area of the unit sphere is `4π`.** For either orientation `o` of `ℝ³`, the
outward-normal area form `(a, b) ↦ vol(u, a, b)` of the unit sphere integrates to `4π` over the
sphere with its outward-normal orientation. -/
theorem Orientation.integralTopForm_sphereOrientation_sphereTopForm
    (o : Orientation ℝ ℝ³ (Fin 3)) :
    TauCeti.integralTopForm o.sphereOrientation o.sphereTopForm = 4 * Real.pi := by
  rcases o.eq_or_eq_neg (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation (by simp)
    with rfl | rfl
  · exact TauCeti.integralTopForm_sphereTopForm_basisFun
  · -- Reversing `o` reverses both the orientation of the sphere and the sign of the form.
    have hneg : (-(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation).sphereTopForm =
        (-1 : ℝ) • (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereTopForm := by
      funext u
      ext v
      simp [Orientation.sphereTopForm_apply, Orientation.volumeForm_neg_orientation]
    rw [Orientation.sphereOrientation_neg, hneg, TauCeti.integralTopForm_neg,
      TauCeti.integralTopForm_smul, TauCeti.integralTopForm_sphereTopForm_basisFun]
    ring
