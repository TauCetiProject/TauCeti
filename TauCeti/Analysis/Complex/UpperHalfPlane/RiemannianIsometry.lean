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
import TauCeti.Geometry.Manifold.Algebra.SMul

/-!
# `GL(2, ℝ)` acts on the upper half-plane by Riemannian isometries

Mathlib's action `UpperHalfPlane.glAction` lets `g = [[a, b], [c, d]]` act on `ℍ` by
`z ↦ (az + b)/(cz + d)` when `det g > 0` and by `z ↦ (a conj z + b)/(c conj z + d)` when
`det g < 0`. This file shows that every such map is a smooth Riemannian isometry of the Poincaré
metric `(Re v Re w + Im v Im w)/y²`, so that the action is a group homomorphism into the
Riemannian isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.

The differential of `z ↦ g • z` is Mathlib's real derivative `UpperHalfPlane.smulFDeriv g z`
(`Matrix.GeneralLinearGroup.tangentSpaceCastModel_mfderiv_smul`), which multiplies real inner
products by `(Im(g • z)/Im z)²` (`Matrix.GeneralLinearGroup.inner_smulFDeriv_apply`). The Poincaré
tensor divides the Euclidean one by the squared height, so these two factors cancel.

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
    _root_.UpperHalfPlane.poincareRiemannianMetric_inner,
    Matrix.GeneralLinearGroup.tangentSpaceCastModel_mfderiv_smul,
    Matrix.GeneralLinearGroup.tangentSpaceCastModel_mfderiv_smul,
    Matrix.GeneralLinearGroup.inner_smulFDeriv_apply]
  have hz := z.im_pos.ne'
  have hgz := (g • z).im_pos.ne'
  field_simp

/-- The action of `g ∈ GL(2, ℝ)` on `ℍ` as a Riemannian isometry of the Poincaré metric. -/
private def smulIsom (g : GL (Fin 2) ℝ) : Isom 𝓘(ℝ, ℂ) ℍ where
  toDiffeomorph := Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g
  inner_mfderiv' z v w := by
    rw [Diffeomorph.coe_constSmul]
    -- The inner product on `TangentSpace 𝓘(ℝ, ℂ) z` is `poincareRiemannianMetric.inner z` by
    -- `instRiemannianBundle`; `change` states the goal in these terms so the metric lemma applies.
    change poincareRiemannianMetric.inner (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) = poincareRiemannianMetric.inner z v w
    exact inner_mfderiv_smul g z v w

/-- The Riemannian isometry attached to `g ∈ GL(2, ℝ)` acts by `g`. -/
private theorem smulIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : smulIsom g z = g • z :=
  Diffeomorph.constSmul_apply g z

/-- **`GL(2, ℝ)` acts on `ℍ` by Riemannian isometries of the Poincaré metric**: the action of
Mathlib's `UpperHalfPlane.glAction`, including its antiholomorphic elements of negative
determinant, as a homomorphism to the Riemannian isometry group. -/
def glIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ where
  toFun := smulIsom
  map_one' := RiemannianIsometry.ext fun z ↦ by
    rw [smulIsom_apply, one_smul, RiemannianIsometry.one_apply]
  map_mul' g h := RiemannianIsometry.ext fun z ↦ by
    rw [RiemannianIsometry.mul_apply, smulIsom_apply, smulIsom_apply, smulIsom_apply, mul_smul]

end TauCeti.UpperHalfPlane

open TauCeti TauCeti.UpperHalfPlane

namespace Matrix.GeneralLinearGroup

/-- The Riemannian isometry attached to `g ∈ GL(2, ℝ)` acts by `g`. -/
@[simp]
theorem glIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glIsom g z = g • z :=
  smulIsom_apply g z

/-- The inverse of the Riemannian isometry attached to `g ∈ GL(2, ℝ)` acts by `g⁻¹`. -/
@[simp]
theorem glIsom_symm_apply (g : GL (Fin 2) ℝ) (z : ℍ) : (glIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, glIsom_apply]

/-- As a function, the Riemannian isometry attached to `g ∈ GL(2, ℝ)` is `(g • ·)`. -/
theorem coe_glIsom (g : GL (Fin 2) ℝ) : ⇑(glIsom g) = (g • ·) :=
  funext (glIsom_apply g)

/-- As a function, the inverse of the Riemannian isometry attached to `g ∈ GL(2, ℝ)` is
`(g⁻¹ • ·)`. -/
theorem coe_glIsom_symm (g : GL (Fin 2) ℝ) : ⇑(glIsom g).symm = (g⁻¹ • ·) :=
  funext (glIsom_symm_apply g)

end Matrix.GeneralLinearGroup

namespace Units

/-- Nonzero scalar matrices act on `ℍ` by the identity isometry. -/
@[simp]
theorem glIsom_scalar (u : ℝˣ) : glIsom (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  RiemannianIsometry.ext fun z ↦ by
    rw [Matrix.GeneralLinearGroup.glIsom_apply, glScalar_smul, RiemannianIsometry.one_apply]

end Units

namespace TauCeti.UpperHalfPlane

/-- **`PGL(2, ℝ)` acts on `ℍ` by Riemannian isometries of the Poincaré metric**: the descent of
`glIsom` to the quotient by the centre, which acts trivially. -/
def pglIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  Matrix.ProjGenLinGroup.lift glIsom (MonoidHom.ext Units.glIsom_scalar)

end TauCeti.UpperHalfPlane

namespace Matrix.GeneralLinearGroup

/-- On the class of `g ∈ GL(2, ℝ)`, the isometry attached to `PGL(2, ℝ)` is that of `g`. -/
@[simp]
theorem pglIsom_mk (g : GL (Fin 2) ℝ) : pglIsom (Matrix.ProjGenLinGroup.mk g) = glIsom g :=
  Matrix.ProjGenLinGroup.lift_mk _ g

end Matrix.GeneralLinearGroup

namespace TauCeti.UpperHalfPlane

/-- `glIsom` factors through the quotient map `GL(2, ℝ) → PGL(2, ℝ)`. -/
@[simp]
theorem pglIsom_comp_mk : pglIsom.comp Matrix.ProjGenLinGroup.mk = glIsom :=
  Matrix.ProjGenLinGroup.lift_comp_mk _

end TauCeti.UpperHalfPlane

namespace Matrix.ProjGenLinGroup

/-- The Riemannian isometry attached to `g ∈ PGL(2, ℝ)` acts by `g`. -/
@[simp]
theorem pglIsom_apply (g : PGL(2, ℝ)) (z : ℍ) : pglIsom g z = g • z := by
  induction g using induction_on with | mk g =>
  rw [Matrix.GeneralLinearGroup.pglIsom_mk, Matrix.GeneralLinearGroup.glIsom_apply, pglMk_smul]

/-- The inverse of the Riemannian isometry attached to `g ∈ PGL(2, ℝ)` acts by `g⁻¹`. -/
@[simp]
theorem pglIsom_symm_apply (g : PGL(2, ℝ)) (z : ℍ) : (pglIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, pglIsom_apply]

/-- As a function, the Riemannian isometry attached to `g ∈ PGL(2, ℝ)` is `(g • ·)`. -/
theorem coe_pglIsom (g : PGL(2, ℝ)) : ⇑(pglIsom g) = (g • ·) :=
  funext (pglIsom_apply g)

/-- As a function, the inverse of the Riemannian isometry attached to `g ∈ PGL(2, ℝ)` is
`(g⁻¹ • ·)`. -/
theorem coe_pglIsom_symm (g : PGL(2, ℝ)) : ⇑(pglIsom g).symm = (g⁻¹ • ·) :=
  funext (pglIsom_symm_apply g)

end Matrix.ProjGenLinGroup

namespace TauCeti.UpperHalfPlane

/-- Distinct elements of `PGL(2, ℝ)` give distinct isometries of `ℍ`. -/
theorem pglIsom_injective : Function.Injective pglIsom := fun g h hgh ↦
  eq_of_smul_eq_smul fun z : ℍ ↦ by
    rw [← Matrix.ProjGenLinGroup.pglIsom_apply, ← Matrix.ProjGenLinGroup.pglIsom_apply, hgh]

/-- The elements of `GL(2, ℝ)` acting on `ℍ` by the identity isometry are the scalar matrices,
which form the centre. -/
@[simp]
theorem ker_glIsom : glIsom.ker = Subgroup.center (GL (Fin 2) ℝ) := by
  rw [← pglIsom_comp_mk, MonoidHom.ker_comp_of_injective _ _ pglIsom_injective,
    Matrix.ProjGenLinGroup.ker_mk]

/-- **`PSL(2, ℝ)` acts on `ℍ` by Riemannian isometries of the Poincaré metric**, through
`PGL(2, ℝ)`. -/
def pslIsom : PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  pglIsom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL

end TauCeti.UpperHalfPlane

namespace Matrix.ProjectiveSpecialLinearGroup

/-- Along `toPGL`, the isometry attached to `PGL(2, ℝ)` is that attached to `PSL(2, ℝ)`. -/
@[simp]
theorem pglIsom_toPGL (g : PSL(2, ℝ)) :
    pglIsom (toPGL g) = pslIsom g :=
  (MonoidHom.comp_apply _ _ g).symm

end Matrix.ProjectiveSpecialLinearGroup

namespace TauCeti.UpperHalfPlane

/-- `pslIsom` factors through `toPGL : PSL(2, ℝ) → PGL(2, ℝ)`. -/
@[simp]
theorem pglIsom_comp_toPGL : pglIsom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL = pslIsom :=
  MonoidHom.ext Matrix.ProjectiveSpecialLinearGroup.pglIsom_toPGL

end TauCeti.UpperHalfPlane

namespace Matrix.SpecialLinearGroup

/-- On the class of `g ∈ SL(2, ℝ)`, the isometry attached to `PSL(2, ℝ)` is that of `g` viewed
in `GL(2, ℝ)`. -/
@[simp]
theorem pslIsom_mk (g : SL(2, ℝ)) :
    pslIsom (g : PSL(2, ℝ)) = glIsom (toGL g) := by
  rw [← Matrix.ProjectiveSpecialLinearGroup.pglIsom_toPGL,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.GeneralLinearGroup.pglIsom_mk]

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The Riemannian isometry attached to `g ∈ PSL(2, ℝ)` acts by `g`. -/
@[simp]
theorem pslIsom_apply (g : PSL(2, ℝ)) (z : ℍ) : pslIsom g z = g • z := by
  rw [← pglIsom_toPGL, Matrix.ProjGenLinGroup.pglIsom_apply, toPGL_smul]

/-- The inverse of the Riemannian isometry attached to `g ∈ PSL(2, ℝ)` acts by `g⁻¹`. -/
@[simp]
theorem pslIsom_symm_apply (g : PSL(2, ℝ)) (z : ℍ) : (pslIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, pslIsom_apply]

/-- As a function, the Riemannian isometry attached to `g ∈ PSL(2, ℝ)` is `(g • ·)`. -/
theorem coe_pslIsom (g : PSL(2, ℝ)) : ⇑(pslIsom g) = (g • ·) :=
  funext (pslIsom_apply g)

/-- As a function, the inverse of the Riemannian isometry attached to `g ∈ PSL(2, ℝ)` is
`(g⁻¹ • ·)`. -/
theorem coe_pslIsom_symm (g : PSL(2, ℝ)) : ⇑(pslIsom g).symm = (g⁻¹ • ·) :=
  funext (pslIsom_symm_apply g)

end Matrix.ProjectiveSpecialLinearGroup

namespace TauCeti.UpperHalfPlane

/-- Distinct elements of `PSL(2, ℝ)` give distinct isometries of `ℍ`. -/
theorem pslIsom_injective : Function.Injective pslIsom :=
  pglIsom_injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

end TauCeti.UpperHalfPlane
