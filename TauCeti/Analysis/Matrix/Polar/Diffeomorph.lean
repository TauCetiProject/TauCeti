/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan
public import TauCeti.Geometry.Manifold.Instances.PositiveDefiniteMatrix
import TauCeti.Analysis.Matrix.Polar.Deformation
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# Polar coordinates on the general linear group

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix factors uniquely as `A = P U`, with `P = √(A Aᴴ)`
positive definite and `U` unitary (orthogonal when `𝕜 = ℝ`), and equally uniquely as `A = U Q`
with the same `U` and `Q = √(Aᴴ A) = Uᴴ P U`. This file shows that both factorizations are global
real smooth diffeomorphisms

`posDefOpens n 𝕜 × unitaryGroup n 𝕜 ≃ GL n 𝕜`, `(P, U) ↦ P U`, and
`unitaryGroup n 𝕜 × posDefOpens n 𝕜 ≃ GL n 𝕜`, `(U, Q) ↦ U Q`.

The positive-definite cone `Matrix.posDefOpens n 𝕜` carries its structure of an open subset of
the real vector space of Hermitian matrices, and the unitary group its native embedded-subgroup
structure. The left factorization is assembled directly from the smooth polar factors
`Matrix.GeneralLinearGroup.contMDiff_sqrt_mul_star` and
`Matrix.GeneralLinearGroup.contMDiff_toUnits_polarUnitary`. The right factorization is the Cartan
diffeomorphism `(U, X) ↦ U exp X` (`Matrix.GeneralLinearGroup.cartanDiffeomorph`) read through
exponential coordinates `X ↦ exp X` on the positive-definite cone
(`Matrix.hermitianExpDiffeomorph`).

Both coordinate systems are equivariant for multiplication by unitary matrices on either side:
the polar coordinates of `V A W` are `(V P Vᴴ, V U W)` and `(V U W, Wᴴ Q W)`. Both restrict to the
special linear group, where `det A = 1` exactly when `det P = 1` and `det U = 1`
(`Matrix.SpecialLinearGroup.polarHomeomorph`).

All smooth statements use the real vector-space structures induced by the ℓ² operator norm: to
use them, `open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main declarations

* `Matrix.GeneralLinearGroup.polarDiffeomorph`: the diffeomorphism `(P, U) ↦ P U`, with inverse
  `A ↦ (√(A Aᴴ), A.polarUnitary)`.
* `Matrix.GeneralLinearGroup.rightPolarDiffeomorph`: the diffeomorphism `(U, Q) ↦ U Q`, with
  inverse `A ↦ (A.polarUnitary, √(Aᴴ A))`.
* `Matrix.GeneralLinearGroup.coe_polarDiffeomorph_symm_unitary_mul_mul_unitary_fst`,
  `Matrix.GeneralLinearGroup.polarDiffeomorph_symm_unitary_mul_mul_unitary_snd` and their
  right-hand counterparts: unitary equivariance.
* `Matrix.SpecialLinearGroup.polarHomeomorph`: the restriction of `(P, U) ↦ P U` to the
  determinant-one positive definite matrices and the special unitary group, a homeomorphism onto
  `SL n 𝕜`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1.
-/

public noncomputable section

open NormedSpace
open scoped ContDiff Manifold Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-! ### The left polar coordinates `A = P U` -/

/-- The positive factor `√(A Aᴴ)` of an invertible matrix, as a point of the positive-definite
cone. -/
private def sqrtMulStarPosDef (A : GL n 𝕜) : posDefOpens n 𝕜 :=
  ⟨⟨CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)), (CFC.sqrt_nonneg _).isSelfAdjoint⟩,
    (mem_posDefOpens _).2 (posDef_sqrt_mul_star A)⟩

/-- The invertible matrix `P U` for `P` positive definite and `U` unitary. -/
private def posDefMulUnitary (p : posDefOpens n 𝕜 × unitaryGroup n 𝕜) : GL n 𝕜 :=
  ((mem_posDefOpens _).1 p.1.2).isUnit.unit * Unitary.toUnits p.2

private theorem val_posDefMulUnitary (p : posDefOpens n 𝕜 × unitaryGroup n 𝕜) :
    (posDefMulUnitary p : Matrix n n 𝕜) =
      ((p.1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) * (p.2 : Matrix n n 𝕜) :=
  (rfl)

variable (n 𝕜) in
/-- **Polar coordinates on `GL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`: the map `(P, U) ↦ P U` is a global
real smooth diffeomorphism from the product of the positive-definite cone and the unitary group
(the orthogonal group when `𝕜 = ℝ`) onto the invertible matrices. Its inverse sends `A` to its
polar factors `√(A Aᴴ)` and `A.polarUnitary`.

The cone carries its open-subset structure in the Hermitian matrices, and the unitary group its
native embedded-subgroup structure. To use this diffeomorphism, open the
`Matrix.Norms.L2Operator` scope and enable `Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def polarDiffeomorph : (posDefOpens n 𝕜 × unitaryGroup n 𝕜) ≃ₘ^∞⟮
    𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)).prod (Unitary.model (Matrix n n 𝕜)),
    𝓘(ℝ, Matrix n n 𝕜)⟯ GL n 𝕜 where
  toFun := posDefMulUnitary
  invFun A := (sqrtMulStarPosDef A, A.polarUnitary)
  left_inv p := by
    have hP := ((mem_posDefOpens _).1 p.1.2).posSemidef.nonneg
    have h := (val_posDefMulUnitary p).symm
    exact Prod.ext (Subtype.ext (Subtype.ext (Units.sqrt_mul_star_eq_of_mul_eq _ hP h)))
      (Units.polarUnitary_eq_of_mul_eq _ hP h)
  right_inv A := Units.ext (Units.sqrt_mul_star_mul_polarUnitary A)
  contMDiff_toFun := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    exact (contDiff_mul.comp_contMDiff
      (((contMDiff_coe_posDefOpens (n := n) (𝕜 := 𝕜)).comp contMDiff_fst).prodMk_space
        ((Units.contMDiff_val.comp Unitary.contMDiff_toUnits).comp contMDiff_snd))).congr
      fun p ↦ val_posDefMulUnitary p
  contMDiff_invFun := by
    apply ContMDiff.prodMk
    · apply (TauCeti.ContMDiff.subtypeVal_comp_iff (posDefOpens n 𝕜) _).mp
      refine ((selfAdjointPartL ℝ (Matrix n n 𝕜)).contDiff.contMDiff.comp
        (contMDiff_sqrt_mul_star (n := n) (𝕜 := 𝕜) (k := ∞))).congr fun A ↦ ?_
      exact ((CFC.sqrt_nonneg _).isSelfAdjoint.selfAdjointPart_apply ℝ).symm
    · apply (ContMDiff.iff_comp_isImmersion Unitary.isImmersion_toUnits).mpr
      exact ⟨(contMDiff_coe_polarUnitary (n := n) (𝕜 := 𝕜) (k := ∞)).continuous.subtype_mk _,
        contMDiff_toUnits_polarUnitary⟩

/-- The polar coordinate map sends `(P, U)` to `P U`. -/
@[simp]
theorem val_polarDiffeomorph_apply (p : posDefOpens n 𝕜 × unitaryGroup n 𝕜) :
    (polarDiffeomorph n 𝕜 p : Matrix n n 𝕜) =
      ((p.1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) * (p.2 : Matrix n n 𝕜) :=
  val_posDefMulUnitary p

/-- The positive coordinate of the inverse polar coordinate map is `√(A Aᴴ)`. -/
@[simp]
theorem coe_polarDiffeomorph_symm_apply_fst (A : GL n 𝕜) :
    ((((polarDiffeomorph n 𝕜).symm A).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)) :=
  (rfl)

/-- The unitary coordinate of the inverse polar coordinate map is the polar unitary factor. -/
@[simp]
theorem polarDiffeomorph_symm_apply_snd (A : GL n 𝕜) :
    ((polarDiffeomorph n 𝕜).symm A).2 = A.polarUnitary :=
  (rfl)

/-- **Unitary equivariance of the positive polar coordinate.** The positive factor of `V A W`,
for unitary `V` and `W`, is `V P Vᴴ`, where `P` is the positive factor of `A`. -/
theorem coe_polarDiffeomorph_symm_unitary_mul_mul_unitary_fst (A : GL n 𝕜)
    (V W : unitaryGroup n 𝕜) :
    ((((polarDiffeomorph n 𝕜).symm (Unitary.toUnits V * A * Unitary.toUnits W)).1 :
        selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      (V : Matrix n n 𝕜) *
        ((((polarDiffeomorph n 𝕜).symm A).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
          star (V : Matrix n n 𝕜) := by
  simp only [coe_polarDiffeomorph_symm_apply_fst]
  exact Units.sqrt_unitary_mul_mul_unitary A V W

/-- **Unitary equivariance of the unitary polar coordinate.** The unitary factor of `V A W`, for
unitary `V` and `W`, is `V U W`, where `U` is the unitary factor of `A`. -/
theorem polarDiffeomorph_symm_unitary_mul_mul_unitary_snd (A : GL n 𝕜)
    (V W : unitaryGroup n 𝕜) :
    ((polarDiffeomorph n 𝕜).symm (Unitary.toUnits V * A * Unitary.toUnits W)).2 =
      V * ((polarDiffeomorph n 𝕜).symm A).2 * W := by
  simp only [polarDiffeomorph_symm_apply_snd]
  exact Units.polarUnitary_unitary_mul_mul_unitary A V W

/-! ### The right polar coordinates `A = U Q` -/

variable (n 𝕜) in
/-- **Right polar coordinates on `GL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`: the map `(U, Q) ↦ U Q` is a
global real smooth diffeomorphism from the product of the unitary group (the orthogonal group
when `𝕜 = ℝ`) and the positive-definite cone onto the invertible matrices. Its inverse sends `A`
to `A.polarUnitary` and `√(Aᴴ A)`.

It is the Cartan diffeomorphism `(U, X) ↦ U exp X` composed with the logarithm coordinates of the
positive-definite cone. To use this diffeomorphism, open the `Matrix.Norms.L2Operator` scope and
enable `Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def rightPolarDiffeomorph : (unitaryGroup n 𝕜 × posDefOpens n 𝕜) ≃ₘ^∞⟮
    (Unitary.model (Matrix n n 𝕜)).prod 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜)),
    𝓘(ℝ, Matrix n n 𝕜)⟯ GL n 𝕜 :=
  ((Diffeomorph.refl _ _ _).prodCongr (hermitianExpDiffeomorph n 𝕜 ∞).symm).trans
    (cartanDiffeomorph n 𝕜)

/-- The right polar coordinates are the Cartan coordinates read through the exponential
coordinates `X ↦ exp X` of the positive-definite cone. -/
theorem rightPolarDiffeomorph_eq :
    rightPolarDiffeomorph n 𝕜 =
      ((Diffeomorph.refl _ _ _).prodCongr (hermitianExpDiffeomorph n 𝕜 ∞).symm).trans
        (cartanDiffeomorph n 𝕜) :=
  (rfl)

/-- The right polar coordinate map sends `(U, Q)` to `U Q`. -/
@[simp]
theorem val_rightPolarDiffeomorph_apply (p : unitaryGroup n 𝕜 × posDefOpens n 𝕜) :
    (rightPolarDiffeomorph n 𝕜 p : Matrix n n 𝕜) =
      (p.1 : Matrix n n 𝕜) * ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) := by
  simp only [rightPolarDiffeomorph_eq, Diffeomorph.coe_trans, Diffeomorph.coe_prodCongr,
    Function.comp_apply, val_cartanDiffeomorph_apply, Prod.map_fst, Prod.map_snd,
    Diffeomorph.coe_refl, id_eq, coe_hermitianExpDiffeomorph_symm_apply]
  rw [((mem_posDefOpens _).1 p.2.2).exp_cfc_log]

/-- The unitary coordinate of the inverse right polar coordinate map is the polar unitary factor,
the same as for the left polar coordinates. -/
@[simp]
theorem rightPolarDiffeomorph_symm_apply_fst (A : GL n 𝕜) :
    ((rightPolarDiffeomorph n 𝕜).symm A).1 = A.polarUnitary := by
  simp only [rightPolarDiffeomorph_eq, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    Diffeomorph.prodCongr_symm, Diffeomorph.coe_prodCongr, Function.comp_apply, Prod.map_fst,
    Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq, cartanDiffeomorph_symm_apply_fst]

/-- The positive coordinate of the inverse right polar coordinate map is `√(Aᴴ A)`. -/
@[simp]
theorem coe_rightPolarDiffeomorph_symm_apply_snd (A : GL n 𝕜) :
    ((((rightPolarDiffeomorph n 𝕜).symm A).2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      CFC.sqrt (star (A : Matrix n n 𝕜) * A) := by
  simp only [rightPolarDiffeomorph_eq, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    Diffeomorph.prodCongr_symm, Diffeomorph.coe_prodCongr, Function.comp_apply, Prod.map_snd]
  have hpos : (CFC.sqrt (star (A : Matrix n n 𝕜) * A)).PosDef := by
    simpa only [Units.coe_star, star_star] using posDef_sqrt_mul_star (star A)
  -- The positive coordinate is `exp (log √(Aᴴ A))`.
  calc _ = exp ((((cartanDiffeomorph n 𝕜).symm A).2 : selfAdjoint (Matrix n n 𝕜)) :
          Matrix n n 𝕜) :=
        coe_hermitianExpDiffeomorph_apply ∞ _
    _ = _ := by rw [coe_cartanDiffeomorph_symm_apply_snd, hpos.exp_cfc_log]

/-- The right positive factor `√(Aᴴ A)` is the left positive factor `√(A Aᴴ)` conjugated by the
unitary factor: `Q = Uᴴ P U`. -/
theorem coe_rightPolarDiffeomorph_symm_apply_snd_eq_star_mul_mul (A : GL n 𝕜) :
    ((((rightPolarDiffeomorph n 𝕜).symm A).2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      star (((polarDiffeomorph n 𝕜).symm A).2 : Matrix n n 𝕜) *
        ((((polarDiffeomorph n 𝕜).symm A).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
          (((polarDiffeomorph n 𝕜).symm A).2 : Matrix n n 𝕜) := by
  rw [coe_rightPolarDiffeomorph_symm_apply_snd, coe_polarDiffeomorph_symm_apply_fst,
    polarDiffeomorph_symm_apply_snd]
  exact Units.sqrt_star_mul_eq A

/-- **Unitary equivariance of the right unitary polar coordinate.** The unitary factor of `V A W`,
for unitary `V` and `W`, is `V U W`, where `U` is the unitary factor of `A`. -/
theorem rightPolarDiffeomorph_symm_unitary_mul_mul_unitary_fst (A : GL n 𝕜)
    (V W : unitaryGroup n 𝕜) :
    ((rightPolarDiffeomorph n 𝕜).symm (Unitary.toUnits V * A * Unitary.toUnits W)).1 =
      V * ((rightPolarDiffeomorph n 𝕜).symm A).1 * W := by
  simp only [rightPolarDiffeomorph_symm_apply_fst]
  exact Units.polarUnitary_unitary_mul_mul_unitary A V W

/-- **Unitary equivariance of the right positive polar coordinate.** The right positive factor of
`V A W`, for unitary `V` and `W`, is `Wᴴ Q W`, where `Q` is the right positive factor of `A`. -/
theorem coe_rightPolarDiffeomorph_symm_unitary_mul_mul_unitary_snd (A : GL n 𝕜)
    (V W : unitaryGroup n 𝕜) :
    ((((rightPolarDiffeomorph n 𝕜).symm (Unitary.toUnits V * A * Unitary.toUnits W)).2 :
        selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      star (W : Matrix n n 𝕜) *
        ((((rightPolarDiffeomorph n 𝕜).symm A).2 : selfAdjoint (Matrix n n 𝕜)) :
          Matrix n n 𝕜) * (W : Matrix n n 𝕜) := by
  simp only [coe_rightPolarDiffeomorph_symm_apply_snd]
  refine Units.sqrt_star_mul_eq_of_mul_eq _
    (star_left_conjugate_nonneg (CFC.sqrt_nonneg _) _) (v := V * A.polarUnitary * W) ?_
  -- `(V U W) (Wᴴ Q W) = V (U Q) W = V A W`.
  have hW : (W : Matrix n n 𝕜) * star (W : Matrix n n 𝕜) = 1 := Unitary.mul_star_self_of_mem W.2
  have hA := Units.polarUnitary_mul_sqrt_star_mul A
  simp only [Units.val_mul, Unitary.val_toUnits_apply, Submonoid.coe_mul]
  calc (V : Matrix n n 𝕜) * A.polarUnitary * W *
        (star (W : Matrix n n 𝕜) * CFC.sqrt (star (A : Matrix n n 𝕜) * A) * W)
      = V * A.polarUnitary * ((W : Matrix n n 𝕜) * star (W : Matrix n n 𝕜)) *
          CFC.sqrt (star (A : Matrix n n 𝕜) * A) * W := by simp only [mul_assoc]
    _ = V * (A.polarUnitary * CFC.sqrt (star (A : Matrix n n 𝕜) * A)) * W := by
      rw [hW, mul_one]; simp only [mul_assoc]
    _ = V * A * W := by rw [hA]

end Matrix.GeneralLinearGroup

/-! ### Restriction to the special linear group -/

namespace Matrix.SpecialLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

open GeneralLinearGroup

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The product `P U` of a determinant-one positive definite matrix and a special unitary matrix
has determinant one. -/
private theorem det_mul_of_det_eq_one
    (p : {P : posDefOpens n 𝕜 // ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1} ×
      specialUnitaryGroup n 𝕜) :
    ((((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
      (p.2 : Matrix n n 𝕜)).det = 1 := by
  rw [det_mul, p.1.2, (mem_specialUnitaryGroup_iff.1 p.2.2).2, one_mul]

variable (n 𝕜) in
/-- **Polar coordinates on `SL(n, 𝕜)`**, for `𝕜 = ℝ` or `ℂ`: the map `(P, U) ↦ P U` is a
homeomorphism from the product of the determinant-one positive definite matrices and the special
unitary group (the special orthogonal group when `𝕜 = ℝ`) onto the special linear group. It is the
restriction of `Matrix.GeneralLinearGroup.polarDiffeomorph`: an invertible matrix has determinant
one exactly when both of its polar factors do.

To use this homeomorphism, open the `Matrix.Norms.L2Operator` scope and enable
`Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def polarHomeomorph :
    ({P : posDefOpens n 𝕜 // ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1} ×
      specialUnitaryGroup n 𝕜) ≃ₜ SpecialLinearGroup n 𝕜 where
  toFun p := ⟨_, det_mul_of_det_eq_one p⟩
  invFun g :=
    (⟨((polarDiffeomorph n 𝕜).symm (toGL g)).1, by
        rw [coe_polarDiffeomorph_symm_apply_fst, det_sqrt_mul_star]
        simp⟩,
      ⟨((polarDiffeomorph n 𝕜).symm (toGL g)).2, mem_specialUnitaryGroup_iff.2
        ⟨Subtype.prop _, by
          rw [polarDiffeomorph_symm_apply_snd]
          exact det_polarUnitary_of_det_eq_one (toGL g) (by simp)⟩⟩)
  left_inv p := by
    set q : posDefOpens n 𝕜 × unitaryGroup n 𝕜 :=
      (p.1, Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup p.2)
    have hval : toGL (⟨_, det_mul_of_det_eq_one p⟩ : SpecialLinearGroup n 𝕜) =
        polarDiffeomorph n 𝕜 q :=
      Units.ext ((coe_GL_coe_matrix _).trans (val_polarDiffeomorph_apply q).symm)
    have h := (polarDiffeomorph n 𝕜).symm_apply_apply q
    rw [← hval] at h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg (fun r ↦ (r.2 : Matrix n n 𝕜)) h))
  right_inv g := by
    apply Subtype.ext
    have h := congrArg Units.val ((polarDiffeomorph n 𝕜).apply_symm_apply (toGL g))
    rw [val_polarDiffeomorph_apply] at h
    simpa using h
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_mul.comp (Continuous.prodMk ?_ ?_)) _
    · exact continuous_subtype_val.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
    · exact continuous_subtype_val.comp continuous_snd
  continuous_invFun := by
    have h := (polarDiffeomorph n 𝕜).symm.continuous.comp continuous_toGL
    refine Continuous.prodMk ((continuous_fst.comp h).subtype_mk _) ?_
    exact (continuous_subtype_val.comp (continuous_snd.comp h)).subtype_mk _

/-- The polar coordinate map of `SL(n, 𝕜)` sends `(P, U)` to `P U`. -/
@[simp]
theorem coe_polarHomeomorph_apply
    (p : {P : posDefOpens n 𝕜 // ((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜).det = 1} ×
      specialUnitaryGroup n 𝕜) :
    (polarHomeomorph n 𝕜 p : Matrix n n 𝕜) =
      (((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
        (p.2 : Matrix n n 𝕜) :=
  (rfl)

/-- The positive coordinate of the inverse polar coordinate map of `SL(n, 𝕜)` is `√(g gᴴ)`. -/
@[simp]
theorem coe_polarHomeomorph_symm_apply_fst (g : SpecialLinearGroup n 𝕜) :
    ((((polarHomeomorph n 𝕜).symm g).1 : posDefOpens n 𝕜) : Matrix n n 𝕜) =
      CFC.sqrt ((g : Matrix n n 𝕜) * star (g : Matrix n n 𝕜)) :=
  (rfl)

/-- The unitary coordinate of the inverse polar coordinate map of `SL(n, 𝕜)` is the polar unitary
factor of `g`. -/
@[simp]
theorem coe_polarHomeomorph_symm_apply_snd (g : SpecialLinearGroup n 𝕜) :
    (((polarHomeomorph n 𝕜).symm g).2 : Matrix n n 𝕜) = (toGL g).polarUnitary :=
  (rfl)

end Matrix.SpecialLinearGroup
