/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan
public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Geometry.Manifold.Instances.PositiveDefiniteMatrix

/-!
# Polar coordinates on the general linear group

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix factors uniquely as `A = P U` with `P = √(A Aᴴ)`
positive definite and `U` unitary (orthogonal when `𝕜 = ℝ`)
(`Matrix.GeneralLinearGroup.existsUnique_posDef_mul_unitary`). This file packages the
factorization as a global real smooth diffeomorphism

`Matrix.GeneralLinearGroup.polarDiffeomorph n 𝕜 : GL n 𝕜 ≃ₘ posDefOpens n 𝕜 × unitaryGroup n 𝕜`,

`A ↦ (√(A Aᴴ), U)`, with inverse `(P, U) ↦ P U`. The positive-definite cone
`Matrix.posDefOpens n 𝕜` carries its structure of an open subset of the real vector space of
Hermitian (symmetric) matrices, and the unitary group its native embedded Lie subgroup structure.
Both directions are smooth: the forward map because both polar factors depend smoothly on `A`
(`Matrix.GeneralLinearGroup.contMDiff_sqrt_mul_star`,
`Matrix.GeneralLinearGroup.contMDiff_toUnits_polarUnitary`), the inverse because it is a
product. Writing `A = U (Uᴴ P U)` instead, the right positive factor `Uᴴ P U = √(Aᴴ A)` is the
exponential of the Hermitian coordinate of the Cartan diffeomorphism
`Matrix.GeneralLinearGroup.cartanDiffeomorph`, whose unitary coordinate is again `U`
(`Matrix.GeneralLinearGroup.exp_cartanDiffeomorph_symm_apply_snd`).

The coordinates are equivariant under unitary multiplication on both sides: for unitary `V` and
`W`, the polar coordinates of `V A W` are `(V P Vᴴ, V U W)`. After unfolding the coordinates with
`Matrix.GeneralLinearGroup.coe_polarDiffeomorph_apply_fst` and
`Matrix.GeneralLinearGroup.polarDiffeomorph_apply_snd`, this is exactly the equivariance of the
polar factors, `Units.sqrt_unitary_mul_mul_unitary` and
`Units.polarUnitary_unitary_mul_mul_unitary`.
In particular, right multiplication by a unitary matrix only moves the unitary coordinate
(`Matrix.GeneralLinearGroup.polarDiffeomorph_mul_toUnits`).

They also restrict to determinant one: `det A = 1` exactly when `det P = 1` and `det U = 1`, because
`det P = ‖det A‖` is positive. Hence the polar coordinates restrict to a homeomorphism
`Matrix.SpecialLinearGroup.polarHomeomorph n 𝕜` from `SL(n, 𝕜)` onto the product of the
positive-definite matrices of determinant one with the special unitary group `SU(n)` (`SO(n)` when
`𝕜 = ℝ`).

To state or use the smooth structures, `open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main declarations

* `Matrix.GeneralLinearGroup.polarDiffeomorph`: the polar-coordinate diffeomorphism
  `A ↦ (√(A Aᴴ), U)`.
* `Matrix.GeneralLinearGroup.polarDiffeomorph_mul_toUnits`: right unitary equivariance.
* `Matrix.GeneralLinearGroup.exp_cartanDiffeomorph_symm_apply_snd`: the comparison with the
  Cartan coordinates `A = U exp X`, namely `exp X = Uᴴ P U`.
* `Matrix.GeneralLinearGroup.det_eq_one_iff_polarDiffeomorph`: the determinant-one condition in
  polar coordinates.
* `Matrix.SpecialLinearGroup.polarHomeomorph`: the restricted polar coordinates on `SL(n, 𝕜)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open scoped Manifold ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable (n 𝕜) in
/-- **Polar coordinates on `GL(n, 𝕜)`** for `𝕜 = ℝ` or `ℂ`: the global real smooth diffeomorphism
`A ↦ (√(A Aᴴ), U)` from the invertible matrices onto the product of the positive-definite cone
and the unitary group (the orthogonal group when `𝕜 = ℝ`), whose inverse is `(P, U) ↦ P U`.

To use this diffeomorphism, open the `Matrix.Norms.L2Operator` scope and enable
`Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def polarDiffeomorph : GL n 𝕜 ≃ₘ^∞⟮𝓘(ℝ, Matrix n n 𝕜),
    𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)).prod (Unitary.model (Matrix n n 𝕜))⟯
    posDefOpens n 𝕜 × unitaryGroup n 𝕜 where
  toFun A := (⟨⟨CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)),
    (CFC.sqrt_nonneg _).isSelfAdjoint⟩, (mem_posDefOpens _).2 (posDef_sqrt_mul_star A)⟩,
    A.polarUnitary)
  invFun p := ((mem_posDefOpens _).1 p.1.2).isUnit.unit * Unitary.toUnits p.2
  left_inv A := Units.ext (Units.sqrt_mul_star_mul_polarUnitary A)
  right_inv p := by
    have hp := ((mem_posDefOpens _).1 p.1.2).posSemidef.nonneg
    have h : ((((mem_posDefOpens _).1 p.1.2).isUnit.unit * Unitary.toUnits p.2 : GL n 𝕜) :
        Matrix n n 𝕜) = (p.1.1 : Matrix n n 𝕜) * p.2 := by
      rw [Units.val_mul, IsUnit.unit_spec, Unitary.val_toUnits_apply]
    exact Prod.ext (Subtype.ext (Subtype.ext (Units.sqrt_mul_star_eq_of_mul_eq _ hp h.symm)))
      (Units.polarUnitary_eq_of_mul_eq _ hp h.symm)
  contMDiff_toFun := by
    refine ContMDiff.prodMk ?_ ?_
    · apply (TauCeti.ContMDiff.subtypeVal_comp_iff (posDefOpens n 𝕜) _).mp
      refine ((selfAdjointPartL ℝ (Matrix n n 𝕜)).contDiff.contMDiff.comp
        contMDiff_sqrt_mul_star).congr fun A ↦ ?_
      exact ((CFC.sqrt_nonneg _).isSelfAdjoint.selfAdjointPart_apply ℝ).symm
    · apply (ContMDiff.iff_comp_isImmersion Unitary.isImmersion_toUnits).mpr
      exact ⟨(contMDiff_coe_polarUnitary (n := n) (𝕜 := 𝕜) (k := ∞)).continuous.subtype_mk _,
        contMDiff_toUnits_polarUnitary (n := n) (𝕜 := 𝕜)⟩
  contMDiff_invFun := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have hP : ContMDiff (𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)).prod (Unitary.model (Matrix n n 𝕜)))
        𝓘(ℝ, Matrix n n 𝕜) ∞ (fun p : posDefOpens n 𝕜 × unitaryGroup n 𝕜 ↦
          ((p.1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜)) :=
      ((selfAdjoint.contDiff_subtype_val ℝ).contMDiff.comp contMDiff_subtype_val).comp
        contMDiff_fst
    have hU : ContMDiff (𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)).prod (Unitary.model (Matrix n n 𝕜)))
        𝓘(ℝ, Matrix n n 𝕜) ∞ (fun p : posDefOpens n 𝕜 × unitaryGroup n 𝕜 ↦
          ((p.2 : unitaryGroup n 𝕜) : Matrix n n 𝕜)) :=
      (Units.contMDiff_val.comp Unitary.contMDiff_toUnits).comp contMDiff_snd
    exact (contDiff_mul.comp_contMDiff (hP.prodMk_space hU)).congr fun _ ↦ rfl

/-- The positive coordinate of the polar diffeomorphism is the positive factor `√(A Aᴴ)`. -/
@[simp]
theorem coe_polarDiffeomorph_apply_fst (A : GL n 𝕜) :
    (((polarDiffeomorph n 𝕜 A).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)) := (rfl)

/-- The unitary coordinate of the polar diffeomorphism is the unitary polar factor. -/
@[simp]
theorem polarDiffeomorph_apply_snd (A : GL n 𝕜) :
    (polarDiffeomorph n 𝕜 A).2 = A.polarUnitary := (rfl)

/-- The inverse polar diffeomorphism multiplies the two coordinates. -/
@[simp]
theorem coe_polarDiffeomorph_symm_apply (p : posDefOpens n 𝕜 × unitaryGroup n 𝕜) :
    ((polarDiffeomorph n 𝕜).symm p : Matrix n n 𝕜) =
      ((p.1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) * (p.2 : Matrix n n 𝕜) := (rfl)

/-- The polar coordinates are the unique factorization of `A` as a positive-definite matrix
times a unitary matrix: a pair from the cone and the unitary group is the polar coordinate pair of
`A` exactly when its product is `A`. -/
theorem polarDiffeomorph_eq_iff (A : GL n 𝕜) (p : posDefOpens n 𝕜 × unitaryGroup n 𝕜) :
    polarDiffeomorph n 𝕜 A = p ↔
      ((p.1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) * (p.2 : Matrix n n 𝕜) = A := by
  rw [← coe_polarDiffeomorph_symm_apply, ← Units.ext_iff]
  constructor
  · rintro rfl
    exact (polarDiffeomorph n 𝕜).symm_apply_apply A
  · rintro rfl
    exact (polarDiffeomorph n 𝕜).apply_symm_apply p

/-! ### Unitary equivariance -/

/-- Right multiplication by a unitary matrix fixes the positive polar coordinate and multiplies
the unitary polar coordinate on the right. -/
theorem polarDiffeomorph_mul_toUnits (A : GL n 𝕜) (W : unitaryGroup n 𝕜) :
    polarDiffeomorph n 𝕜 (A * Unitary.toUnits W) =
      ((polarDiffeomorph n 𝕜 A).1, (polarDiffeomorph n 𝕜 A).2 * W) := by
  rw [polarDiffeomorph_eq_iff, coe_polarDiffeomorph_apply_fst, polarDiffeomorph_apply_snd,
    Submonoid.coe_mul, ← mul_assoc, Units.sqrt_mul_star_mul_polarUnitary, Units.val_mul,
    Unitary.val_toUnits_apply]

/-- **Comparison with the Cartan coordinates.** The Cartan decomposition `A = U exp X`
(`Matrix.GeneralLinearGroup.cartanDiffeomorph`) has the same unitary coordinate `U` as the polar
coordinates `A = P U`, and its Hermitian coordinate exponentiates to the right positive factor:
`exp X = Uᴴ P U`, so that `A = U (Uᴴ P U)`. -/
theorem exp_cartanDiffeomorph_symm_apply_snd (A : GL n 𝕜) :
    NormedSpace.exp ((((cartanDiffeomorph n 𝕜).symm A).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      star ((polarDiffeomorph n 𝕜 A).2 : Matrix n n 𝕜) *
        (((polarDiffeomorph n 𝕜 A).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
          ((polarDiffeomorph n 𝕜 A).2 : Matrix n n 𝕜) := by
  rw [coe_cartanDiffeomorph_symm_apply_snd, coe_polarDiffeomorph_apply_fst,
    polarDiffeomorph_apply_snd, ← Units.sqrt_star_mul_eq]
  exact PosDef.exp_cfc_log (by simpa using posDef_sqrt_mul_star (star A))

/-! ### Determinant one -/

/-- An invertible matrix has determinant one exactly when both of its polar coordinates have
determinant one. -/
theorem det_eq_one_iff_polarDiffeomorph (A : GL n 𝕜) :
    (A : Matrix n n 𝕜).det = 1 ↔
      (((polarDiffeomorph n 𝕜 A).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1 ∧
        ((polarDiffeomorph n 𝕜 A).2 : Matrix n n 𝕜).det = 1 := by
  refine ⟨fun hA ↦ ⟨?_, det_polarUnitary_of_det_eq_one A hA⟩, fun h ↦ ?_⟩
  · rw [coe_polarDiffeomorph_apply_fst, det_sqrt_mul_star, hA, norm_one, RCLike.ofReal_one]
  · have hA := congrArg Units.val ((polarDiffeomorph n 𝕜).symm_apply_apply A)
    rw [coe_polarDiffeomorph_symm_apply] at hA
    rw [← hA, det_mul, h.1, h.2, mul_one]

end Matrix.GeneralLinearGroup

namespace Matrix.SpecialLinearGroup

open Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable (n 𝕜) in
/-- **Polar coordinates on `SL(n, 𝕜)`** for `𝕜 = ℝ` or `ℂ`: the restriction of the polar
diffeomorphism `Matrix.GeneralLinearGroup.polarDiffeomorph` is a homeomorphism `A ↦ (√(A Aᴴ), U)`
from the special linear group onto the product of the positive-definite matrices of determinant
one with the special unitary group (the special orthogonal group when `𝕜 = ℝ`). Its inverse is
`(P, U) ↦ P U`. -/
def polarHomeomorph : SpecialLinearGroup n 𝕜 ≃ₜ
    {P : posDefOpens n 𝕜 // ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1} ×
      specialUnitaryGroup n 𝕜 where
  toFun g :=
    have h := (det_eq_one_iff_polarDiffeomorph (toGL g)).1 g.2
    (⟨(polarDiffeomorph n 𝕜 (toGL g)).1, h.1⟩,
      ⟨(polarDiffeomorph n 𝕜 (toGL g)).2,
        mem_specialUnitaryGroup_iff.2 ⟨(polarDiffeomorph n 𝕜 (toGL g)).2.2, h.2⟩⟩)
  invFun p := ⟨((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) * (p.2 : Matrix n n 𝕜), by
    rw [det_mul, p.1.2, (mem_specialUnitaryGroup_iff.1 p.2.2).2, mul_one]⟩
  left_inv g := Subtype.ext (Units.sqrt_mul_star_mul_polarUnitary (toGL g))
  right_inv := by
    rintro ⟨⟨P, hP⟩, U, hU⟩
    have h := (polarDiffeomorph_eq_iff (toGL ⟨((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
      (U : Matrix n n 𝕜),
      by rw [det_mul, hP, (mem_specialUnitaryGroup_iff.1 hU).2, mul_one]⟩)
      (P, ⟨U, (mem_specialUnitaryGroup_iff.1 hU).1⟩)).2 rfl
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg (fun q ↦ (q.2 : Matrix n n 𝕜)) h))
  continuous_toFun := by
    have h := (polarDiffeomorph n 𝕜).continuous.comp continuous_toGL
    exact ((continuous_fst.comp h).subtype_mk _).prodMk
      (((continuous_subtype_val.comp (continuous_snd.comp h))).subtype_mk _)
  continuous_invFun := by
    have hP : Continuous fun p : {P : posDefOpens n 𝕜 //
        ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1} × specialUnitaryGroup n 𝕜 ↦
        ((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    exact ((continuous_subtype_val.comp hP).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The positive-definite coordinate of the polar coordinates on `SL(n, 𝕜)` is `√(A Aᴴ)`. -/
@[simp]
theorem coe_polarHomeomorph_apply_fst (g : SpecialLinearGroup n 𝕜) :
    ((((polarHomeomorph n 𝕜 g).1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) = CFC.sqrt ((g : Matrix n n 𝕜) * star (g : Matrix n n 𝕜)) := (rfl)

/-- The special unitary coordinate of the polar coordinates on `SL(n, 𝕜)` is the unitary polar
factor. -/
@[simp]
theorem coe_polarHomeomorph_apply_snd (g : SpecialLinearGroup n 𝕜) :
    ((polarHomeomorph n 𝕜 g).2 : Matrix n n 𝕜) = (toGL g).polarUnitary := (rfl)

/-- The inverse polar coordinates on `SL(n, 𝕜)` multiply the two coordinates. -/
@[simp]
theorem coe_polarHomeomorph_symm_apply
    (p : {P : posDefOpens n 𝕜 // ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1} ×
      specialUnitaryGroup n 𝕜) :
    ((polarHomeomorph n 𝕜).symm p : Matrix n n 𝕜) =
      (((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
        (p.2 : Matrix n n 𝕜) := (rfl)

end Matrix.SpecialLinearGroup
