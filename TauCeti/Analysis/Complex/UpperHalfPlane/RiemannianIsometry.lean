/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group
-- supplies the `FaithfulSMul PGL(2, ℝ) ℍ` instance behind `pglIsom_injective`
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# `GL(2, ℝ)` acts on the upper half-plane by Riemannian isometries

Mathlib's action `UpperHalfPlane.glAction` lets `g = [[a, b], [c, d]]` act on `ℍ` by
`z ↦ (az + b)/(cz + d)` when `det g > 0` and by `z ↦ (a conj z + b)/(c conj z + d)` when
`det g < 0`. This file shows that every such map is a smooth Riemannian isometry of the Poincaré
metric `(Re v Re w + Im v Im w)/y²`, so that the action is a group homomorphism into the
Riemannian isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.

The differential of `z ↦ g • z` is Mathlib's real derivative `UpperHalfPlane.smulFDeriv g z`
(`UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`), which multiplies real inner products by
`(Im(g • z)/Im z)²` (`UpperHalfPlane.inner_smulFDeriv_apply`). The Poincaré tensor divides the
Euclidean one by the squared height, so these two factors cancel.

## Main declarations

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
