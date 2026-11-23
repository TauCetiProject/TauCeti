/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Analysis.InnerProductSpace.Euclidean.CrossProduct
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic

/-!
# The area form of the two-sphere in stereographic coordinates

Inverse stereographic projection from the south pole `(0, 0, -1)` of the unit sphere `S² ⊂ ℝ³`,

`q(x, y) = (2x, 2y, 1 - x² - y²) / (1 + x² + y²)`

(`TauCeti.stereoSphere`), is Mathlib's `stereoInvFunAux` from the south pole read on the
equatorial plane through `(x, y) ↦ (2x, 2y, 0)`. It is a smooth open embedding of `ℝ²` onto the
sphere minus the south pole. Its derivative is given by `TauCeti.fderiv_stereoInvFunAux_apply`,
and in coordinates the triple product of `q` with its two partial derivatives is
`4 / (1 + x² + y²)²`. So `q` pulls the outward-normal area form `u ⬝ᵥ (a ⨯₃ b)` of the sphere
back to `4 / (1 + x² + y²)² dx ∧ dy`.

## Main definitions

* `TauCeti.stereoSphere`: inverse stereographic projection from the south pole, as a map
  `ℝ² → S²`.
* `TauCeti.sphereSouthPole`: the south pole `(0, 0, -1)` of `S²`.

## Main results

* `TauCeti.isOpenEmbedding_stereoSphere`, `TauCeti.range_stereoSphere`: `stereoSphere` is an open
  embedding of `ℝ²` onto the sphere minus the south pole.
* `TauCeti.sphereVolumeForm_mfderiv_stereoSphere_apply`: it pulls the area form back to
  `4 / (1 + x² + y²)² dx ∧ dy`.
-/

public section

noncomputable section

open Metric Module Matrix
open scoped Manifold ContDiff

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => sphere (0 : ℝ³) 1

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

private theorem planeEmbed_mem_orthogonal (z : ℝ²) : planeEmbed z ∈ (ℝ ∙ southPoleVec)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [planeEmbed_apply, southPoleVec, dotProduct, Fin.sum_univ_three]

private theorem stereoParam_mem_sphere (z : ℝ²) : stereoParam z ∈ S² :=
  stereoInvFunAux_mem norm_southPoleVec (planeEmbed_mem_orthogonal z)

private theorem contDiff_stereoParam : ContDiff ℝ ∞ stereoParam :=
  contDiff_stereoInvFunAux.comp planeEmbed.contDiff

private theorem fderiv_stereoParam_apply (z a : ℝ²) :
    fderiv ℝ stereoParam z a =
      fderiv ℝ (stereoInvFunAux southPoleVec) (planeEmbed z) (planeEmbed a) := by
  -- `stereoParam` is by definition the composite `stereoInvFunAux southPoleVec ∘ planeEmbed`,
  -- so the chain rule for that composite is its derivative.
  have h : HasFDerivAt stereoParam
      ((fderiv ℝ (stereoInvFunAux southPoleVec) (planeEmbed z)).comp planeEmbed) z :=
    ((contDiff_stereoInvFunAux (v := southPoleVec) (m := 1)).differentiable
      one_ne_zero _).hasFDerivAt.comp z planeEmbed.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply]

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

/-- Inverse stereographic projection from the south pole, as a map into the unit sphere:
`(x, y) ↦ (2x, 2y, 1 - x² - y²) / (1 + x² + y²)`. It is a smooth injective parametrization of the
sphere minus the south pole (`TauCeti.range_stereoSphere`, `TauCeti.isOpenEmbedding_stereoSphere`)
which pulls the area form back to `4 / (1 + x² + y²)² dx ∧ dy`
(`TauCeti.sphereVolumeForm_mfderiv_stereoSphere_apply`). -/
def stereoSphere : ℝ² → S² :=
  Set.codRestrict stereoParam _ stereoParam_mem_sphere

/-- In coordinates, inverse stereographic projection from the south pole is
`(x, y) ↦ (2x, 2y, 1 - x² - y²) / (1 + x² + y²)`. -/
theorem coe_stereoSphere (z : ℝ²) :
    (stereoSphere z : ℝ³) = WithLp.toLp 2 ![2 * z 0 / (1 + z 0 ^ 2 + z 1 ^ 2),
      2 * z 1 / (1 + z 0 ^ 2 + z 1 ^ 2), (1 - z 0 ^ 2 - z 1 ^ 2) / (1 + z 0 ^ 2 + z 1 ^ 2)] :=
  stereoParam_eq z

/-- Inverse stereographic projection from the south pole is smooth. -/
theorem contMDiff_stereoSphere : ContMDiff 𝓘(ℝ, ℝ²) (𝓡 2) ∞ stereoSphere :=
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
private theorem sphereVolumeForm_mfderiv_stereoSphere (z : ℝ²) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val (stereoSphere z)
      (fun i ↦ mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i)) =
        4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 := by
  rw [Orientation.sphereVolumeForm_apply, ← dotProduct_cross_fderiv_stereoParam,
    ← EuclideanSpace.volumeForm_basisFun_orientation_three]
  refine congrArg _ (funext fun i ↦ ?_)
  fin_cases i
  · rfl
  · exact (mvfderiv_coe_mfderiv_stereoSphere z _).trans
      (by simp [EuclideanSpace.basisFun_apply])
  · exact (mvfderiv_coe_mfderiv_stereoSphere z _).trans
      (by simp [EuclideanSpace.basisFun_apply])

/-- On the derivatives of inverse stereographic projection from the south pole, the area form is
`4 / (1 + x² + y²)²` times the determinant `a₀ b₁ - a₁ b₀` of the two tangent vectors. -/
theorem sphereVolumeForm_mfderiv_stereoSphere_apply (z a b : ℝ²) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val (stereoSphere z)
      ![mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z a, mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z b] =
        4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 * (a 0 * b 1 - a 1 * b 0) := by
  set e := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  set L : ℝ² →ₗ[ℝ] ℝ² := (mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z : ℝ² →L[ℝ] ℝ²).toLinearMap
  -- The pulled back form is an alternating form on `ℝ²`, so it is its value on the standard basis
  -- times the determinant.
  set f := ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val
    (stereoSphere z)).toAlternatingMap.compLinearMap L
  have h := congrArg (fun g ↦ g ![a, b]) (f.eq_smul_basis_det e)
  have hf : f e = 4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2 := sphereVolumeForm_mfderiv_stereoSphere z
  have hfab : f ![a, b] = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val
      (stereoSphere z) ![mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z a,
        mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere z b] := by
    exact congrArg ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm.val
      (stereoSphere z)) (funext fun i ↦ by fin_cases i <;> rfl)
  rw [← hfab, h]
  simp only [smul_apply, hf, smul_eq_mul, Module.Basis.det_apply, Matrix.det_fin_two,
    Module.Basis.toMatrix_apply]
  simp only [e, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-! ### The image of the parametrization -/

/-- The identification `z ↦ (2 z₀, 2 z₁, 0)` of `ℝ²` with the plane orthogonal to the south
pole. -/
private def planeMk (z : ℝ²) : (ℝ ∙ southPoleVec)ᗮ :=
  ⟨planeEmbed z, planeEmbed_mem_orthogonal z⟩

private theorem injective_planeMk : Function.Injective planeMk := by
  intro z w h
  have h' (i : Fin 3) := congrArg (fun p : (ℝ ∙ southPoleVec)ᗮ ↦ (p : ℝ³) i) h
  ext i
  fin_cases i
  · simpa [planeMk, planeEmbed_apply] using h' 0
  · simpa [planeMk, planeEmbed_apply] using h' 1

private theorem surjective_planeMk : Function.Surjective planeMk := by
  rintro ⟨w, hw⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    EuclideanSpace.inner_eq_star_dotProduct] at hw
  have hw2 : w 2 = 0 := by simpa [southPoleVec, dotProduct, Fin.sum_univ_three] using hw
  refine ⟨WithLp.toLp 2 ![w 0 / 2, w 1 / 2], Subtype.ext ?_⟩
  ext i
  fin_cases i <;> simp [planeMk, planeEmbed_apply, hw2, mul_div_cancel₀]

/-- The parametrization is Mathlib's inverse stereographic projection from the south pole, read
on `ℝ²` through `planeMk`. -/
private theorem stereoSphere_eq_comp :
    stereoSphere = (stereographic norm_southPoleVec).symm ∘ planeMk :=
  rfl

/-- Inverse stereographic projection from the south pole is injective. -/
theorem injective_stereoSphere : Function.Injective stereoSphere := by
  rw [stereoSphere_eq_comp]
  exact (isOpenEmbedding_stereographic_symm norm_southPoleVec).injective.comp injective_planeMk

/-- The south pole `(0, 0, -1)` of the unit sphere of `ℝ³`. -/
def sphereSouthPole : S² :=
  ⟨southPoleVec, mem_sphere_zero_iff_norm.2 norm_southPoleVec⟩

/-- The south pole of `S²` is the vector `(0, 0, -1)` of `ℝ³`. -/
@[simp]
theorem coe_sphereSouthPole : (sphereSouthPole : ℝ³) = WithLp.toLp 2 ![0, 0, -1] :=
  (rfl)

/-- Inverse stereographic projection from the south pole covers exactly the sphere minus the
south pole. -/
theorem range_stereoSphere : Set.range stereoSphere = {sphereSouthPole}ᶜ := by
  rw [stereoSphere_eq_comp, Set.range_comp, surjective_planeMk.range_eq, Set.image_univ,
    range_stereographic_symm]
  rfl

/-- Inverse stereographic projection from the south pole is an open embedding of `ℝ²` into the
unit sphere. -/
theorem isOpenEmbedding_stereoSphere : Topology.IsOpenEmbedding stereoSphere := by
  rw [stereoSphere_eq_comp]
  -- `planeMk` is a continuous linear bijection onto a finite-dimensional space, hence open.
  set P : ℝ² →L[ℝ] (ℝ ∙ southPoleVec)ᗮ :=
    planeEmbed.codRestrict _ planeEmbed_mem_orthogonal
  have hP : ⇑P = planeMk := rfl
  refine (isOpenEmbedding_stereographic_symm norm_southPoleVec).comp ?_
  rw [← hP]
  exact .of_continuous_injective_isOpenMap P.continuous (hP ▸ injective_planeMk)
    (P.isOpenMap (hP ▸ surjective_planeMk))

end TauCeti
