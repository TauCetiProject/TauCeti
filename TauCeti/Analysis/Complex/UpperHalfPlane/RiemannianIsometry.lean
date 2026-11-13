/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group
-- supplies the `FaithfulSMul PGL(2, ℝ) ℍ` instance behind `pglIsom_injective`
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# `GL(2, ℝ)` acts on the upper half-plane by Riemannian isometries

Mathlib's action `UpperHalfPlane.glAction` lets `g = [[a, b], [c, d]]` act on `ℍ` by
`z ↦ (az + b)/(cz + d)` when `det g > 0` and by `z ↦ (a conj z + b)/(c conj z + d)` when
`det g < 0`. This file shows that every such map is a smooth Riemannian isometry of the Poincaré
metric `(Re v Re w + Im v Im w)/y²`, so that the action is a group homomorphism into the
Riemannian isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.

The real derivative of `z ↦ g • z` is Mathlib's `UpperHalfPlane.smulFDeriv g z`: multiplication by
`det g/(cz + d)²`, followed by complex conjugation when `det g < 0`. It multiplies every tangent
vector's length by `|det g|/|cz + d|²`, which is the ratio `Im(g • z)/Im z` by
`UpperHalfPlane.im_smul_eq_div_normSq`. The Poincaré tensor divides the Euclidean one by the
squared height, so these two factors cancel.

## Main declarations

* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: in model coordinates, the differential of
  the action of `g ∈ GL(2, ℝ)`, smooth by `UpperHalfPlane.instContMDiffConstSMulGL2Real`, is
  `UpperHalfPlane.smulFDeriv`.
* `UpperHalfPlane.inner_smulFDeriv_apply`: `UpperHalfPlane.smulFDeriv g z` multiplies real inner
  products by `(Im(g • z)/Im z)²`.
* `TauCeti.UpperHalfPlane.glIsom`: the action of `GL(2, ℝ)` on `ℍ` by Riemannian isometries of the
  Poincaré metric.
* `TauCeti.UpperHalfPlane.pglIsom` and `TauCeti.UpperHalfPlane.pslIsom`: the induced injective
  homomorphisms from `PGL(2, ℝ)` and `PSL(2, ℝ)` to the isometry group.

## References

* Svetlana Katok, *Fuchsian Groups*, §1.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 3 (the upper half-plane
  model).
-/

public section

open UpperHalfPlane Manifold
open scoped ContDiff MatrixGroups Manifold

noncomputable section

/-- In the model coordinates of the inclusion chart, the differential of the action of
`g ∈ GL(2, ℝ)` on `ℍ` is Mathlib's real derivative `UpperHalfPlane.smulFDeriv g z`. -/
theorem UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z :=
    (contMDiff_const_smul (n := 1) g).mdifferentiableAt one_ne_zero
  rw [hg.tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • ·)
      =ᶠ[nhds (z : ℂ)] fun w ↦ ↑(g • ofComplex w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have hsymm : (extChartAt 𝓘(ℝ, ℂ) z).symm w = ofComplex w := by
      rw [ofComplex_apply_of_im_pos hw]
      exact (extChartAt 𝓘(ℝ, ℂ) z).left_inv (x := ⟨w, hw⟩) (by simp)
    simp only [writtenInExtChartAt, Function.comp_apply, hsymm]
    simp
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, (hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

/-- The real derivative of the action of `g ∈ GL(2, ℝ)` multiplies lengths by
`Im(g • z)/Im z`. -/
theorem UpperHalfPlane.norm_smulFDeriv_apply (g : GL (Fin 2) ℝ) (z : ℍ) (v : ℂ) :
    ‖smulFDeriv g z v‖ = (g • z).im / z.im * ‖v‖ := by
  have hz := z.im_pos.ne'
  have hd := denom_ne_zero g z
  rw [im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  simp only [smulFDeriv, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    ContinuousAlgEquiv.toContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, norm_σ,
    norm_smul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  field_simp

/-- The real derivative of the action of `g ∈ GL(2, ℝ)` multiplies real inner products by
`(Im(g • z)/Im z)²`. -/
theorem UpperHalfPlane.inner_smulFDeriv_apply (g : GL (Fin 2) ℝ) (z : ℍ) (v w : ℂ) :
    inner ℝ (smulFDeriv g z v) (smulFDeriv g z w) = ((g • z).im / z.im) ^ 2 * inner ℝ v w := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
    norm_smulFDeriv_apply, norm_smulFDeriv_apply, norm_smulFDeriv_apply]
  ring

namespace TauCeti.UpperHalfPlane

/-- The differential of the action of `g ∈ GL(2, ℝ)` preserves the Poincaré inner product. -/
private theorem inner_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    poincareRiemannianMetric.inner (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      poincareRiemannianMetric.inner z v w := by
  rw [_root_.UpperHalfPlane.poincareRiemannianMetric_inner,
    _root_.UpperHalfPlane.poincareRiemannianMetric_inner, tangentSpaceCastModel_mfderiv_smul,
    tangentSpaceCastModel_mfderiv_smul, inner_smulFDeriv_apply]
  have hz := z.im_pos.ne'
  have hgz := (g • z).im_pos.ne'
  field_simp

/-- The action of `g ∈ GL(2, ℝ)` on `ℍ` as a Riemannian isometry of the Poincaré metric. -/
private def smulIsom (g : GL (Fin 2) ℝ) : Isom 𝓘(ℝ, ℂ) ℍ where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := contMDiff_const_smul g
  contMDiff_invFun := contMDiff_const_smul g⁻¹
  inner_mfderiv' := inner_mfderiv_smul g

/-- The Riemannian isometry attached to `g ∈ GL(2, ℝ)` acts by `g`. -/
private theorem smulIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : smulIsom g z = g • z := (rfl)

/-- **`GL(2, ℝ)` acts on `ℍ` by Riemannian isometries of the Poincaré metric**: the action of
Mathlib's `UpperHalfPlane.glAction`, including its antiholomorphic elements of negative
determinant, as a homomorphism to the Riemannian isometry group. -/
def glIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ where
  toFun := smulIsom
  map_one' := RiemannianIsometry.ext fun z ↦ by
    rw [smulIsom_apply, one_smul, RiemannianIsometry.one_apply]
  map_mul' g h := RiemannianIsometry.ext fun z ↦ by
    rw [RiemannianIsometry.mul_apply, smulIsom_apply, smulIsom_apply, smulIsom_apply, mul_smul]

/-- The Riemannian isometry attached to `g ∈ GL(2, ℝ)` acts by `g`. -/
@[simp]
theorem glIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glIsom g z = g • z :=
  smulIsom_apply g z

/-- The inverse of the Riemannian isometry attached to `g ∈ GL(2, ℝ)` acts by `g⁻¹`. -/
@[simp]
theorem glIsom_symm_apply (g : GL (Fin 2) ℝ) (z : ℍ) : (glIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, glIsom_apply]

/-- **`PGL(2, ℝ)` acts on `ℍ` by Riemannian isometries of the Poincaré metric**: the descent of
`glIsom` to the quotient by the centre, which acts trivially. -/
def pglIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  QuotientGroup.lift _ glIsom fun g hg ↦ RiemannianIsometry.ext fun z ↦ by
    rw [glIsom_apply, RiemannianIsometry.one_apply, ← pglMk_smul,
      Matrix.ProjGenLinGroup.mk_eq_one.mpr hg, one_smul]

/-- On the class of `g ∈ GL(2, ℝ)`, the isometry attached to `PGL(2, ℝ)` is that of `g`. -/
@[simp]
theorem pglIsom_mk (g : GL (Fin 2) ℝ) : pglIsom (Matrix.ProjGenLinGroup.mk g) = glIsom g :=
  -- `PGL(2, ℝ)` is the quotient by the centre and `mk` its quotient map, so the lift computes.
  (rfl)

/-- The Riemannian isometry attached to `g ∈ PGL(2, ℝ)` acts by `g`. -/
@[simp]
theorem pglIsom_apply (g : PGL(2, ℝ)) (z : ℍ) : pglIsom g z = g • z := by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  rw [pglIsom_mk, glIsom_apply, pglMk_smul]

/-- The inverse of the Riemannian isometry attached to `g ∈ PGL(2, ℝ)` acts by `g⁻¹`. -/
@[simp]
theorem pglIsom_symm_apply (g : PGL(2, ℝ)) (z : ℍ) : (pglIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, pglIsom_apply]

/-- Distinct elements of `PGL(2, ℝ)` give distinct isometries of `ℍ`. -/
theorem pglIsom_injective : Function.Injective pglIsom := fun g h hgh ↦
  eq_of_smul_eq_smul fun z : ℍ ↦ by
    rw [← pglIsom_apply, ← pglIsom_apply, hgh]

/-- **`PSL(2, ℝ)` acts on `ℍ` by Riemannian isometries of the Poincaré metric**, through
`PGL(2, ℝ)`. -/
def pslIsom : PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  pglIsom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL

/-- The Riemannian isometry attached to `g ∈ PSL(2, ℝ)` acts by `g`. -/
@[simp]
theorem pslIsom_apply (g : PSL(2, ℝ)) (z : ℍ) : pslIsom g z = g • z := by
  simp [pslIsom]

/-- The inverse of the Riemannian isometry attached to `g ∈ PSL(2, ℝ)` acts by `g⁻¹`. -/
@[simp]
theorem pslIsom_symm_apply (g : PSL(2, ℝ)) (z : ℍ) : (pslIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, pslIsom_apply]

/-- Distinct elements of `PSL(2, ℝ)` give distinct isometries of `ℍ`. -/
theorem pslIsom_injective : Function.Injective pslIsom :=
  pglIsom_injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

end TauCeti.UpperHalfPlane
