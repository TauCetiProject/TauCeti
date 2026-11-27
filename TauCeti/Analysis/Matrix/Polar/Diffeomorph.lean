/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan.Basic
public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Geometry.Manifold.Instances.PositiveDefiniteMatrix.DetOne
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import TauCeti.Geometry.Manifold.Instances.Unitary.Special
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
import TauCeti.Geometry.Lie.SpecialLinear.RealEmbedding
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Polar coordinates on the general and special linear groups

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
Reading the Cartan coordinates through the exponential coordinates of the cone
(`Matrix.hermitianExpDiffeomorph`) gives the right polar coordinates
`Matrix.GeneralLinearGroup.rightPolarDiffeomorph n 𝕜`,

`rightPolarDiffeomorph n 𝕜 : GL n 𝕜 ≃ₘ unitaryGroup n 𝕜 × posDefOpens n 𝕜`,

`A ↦ (U, √(Aᴴ A))`, with inverse `(U, Q) ↦ U Q`.

The coordinates are equivariant under unitary multiplication on both sides: for unitary `V` and
`W`, the polar coordinates of `V A W` are `(V P Vᴴ, V U W)`
(`Matrix.GeneralLinearGroup.polarDiffeomorph_toUnits_mul_mul_toUnits`), where the unitary group
acts on the positive-definite cone by the conjugation diffeomorphisms `Matrix.posDefUnitaryConj`.
This is the equivariance of the polar factors, `Units.sqrt_unitary_mul_mul_unitary` and
`Units.polarUnitary_unitary_mul_mul_unitary`, read in the coordinates.
In particular, right multiplication by a unitary matrix only moves the unitary coordinate
(`Matrix.GeneralLinearGroup.polarDiffeomorph_mul_toUnits`). Dually, the right polar coordinates
of `V A W` are `(V U W, Wᴴ Q W)`
(`Matrix.GeneralLinearGroup.rightPolarDiffeomorph_toUnits_mul_mul_toUnits`), and left
multiplication by a unitary matrix only moves their unitary coordinate
(`Matrix.GeneralLinearGroup.rightPolarDiffeomorph_toUnits_mul`).

They also restrict to determinant one: `det A = 1` exactly when `det P = 1` and `det U = 1`, because
`det P = ‖det A‖` is positive, and likewise `det √(Aᴴ A) = ‖det A‖` (`Matrix.det_sqrt_star_mul`).
Hence both polar coordinates restrict to global real smooth diffeomorphisms

`Matrix.SpecialLinearGroup.polarDiffeomorph n 𝕜 : SL(n, 𝕜) ≃ₘ PosDefDetOne n 𝕜 × SU(n)`,
`Matrix.SpecialLinearGroup.rightPolarDiffeomorph n 𝕜 : SL(n, 𝕜) ≃ₘ SU(n) × PosDefDetOne n 𝕜`

onto the products of the positive-definite matrices of determinant one
(`Matrix.PosDefDetOne n 𝕜`, with its regular-level structure) with the special unitary group
`SU(n)` (`SO(n)` when `𝕜 = ℝ`, with its native Lie-group structure). The special linear group
carries the real structure of its native analytic atlas. Its inclusion into `GL(n, 𝕜)` is an
injective continuous homomorphism of real Lie groups, hence a smooth immersion, so the matrix
inclusion of `SL(n, 𝕜)` is a real smooth embedding
(`Matrix.SpecialLinearGroup.isSmoothEmbedding_subtypeVal_real`), and the inverse maps
`(P, U) ↦ P U` and `(U, Q) ↦ U Q` are smooth because their matrix products are.

Both restricted coordinates are equivariant under multiplication by special unitary matrices on
both sides, with the unitary group acting on `PosDefDetOne n 𝕜` by conjugation
(`Matrix.PosDefDetOne.unitaryConj`): the polar coordinates of `V g W` are `(V P Vᴴ, V U W)` and its
right polar coordinates are `(V U W, Wᴴ Q W)`
(`Matrix.SpecialLinearGroup.polarDiffeomorph_toSL_mul_mul_toSL`,
`Matrix.SpecialLinearGroup.rightPolarDiffeomorph_toSL_mul_mul_toSL`).

To state or use the smooth structures, `open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main declarations

* `Matrix.GeneralLinearGroup.polarDiffeomorph`: the polar-coordinate diffeomorphism
  `A ↦ (√(A Aᴴ), U)`.
* `Matrix.GeneralLinearGroup.polarDiffeomorph_toUnits_mul_mul_toUnits`: unitary equivariance,
  with the one-sided cases `Matrix.GeneralLinearGroup.polarDiffeomorph_toUnits_mul` and
  `Matrix.GeneralLinearGroup.polarDiffeomorph_mul_toUnits`.
* `Matrix.GeneralLinearGroup.exp_cartanDiffeomorph_symm_apply_snd`: the comparison with the
  Cartan coordinates `A = U exp X`, namely `exp X = Uᴴ P U`.
* `Matrix.GeneralLinearGroup.rightPolarDiffeomorph`: the right polar-coordinate diffeomorphism
  `A ↦ (U, √(Aᴴ A))`.
* `Matrix.GeneralLinearGroup.coe_rightPolarDiffeomorph_apply_snd_eq_star_mul_mul`: the right
  positive coordinate is `Uᴴ P U`.
* `Matrix.GeneralLinearGroup.rightPolarDiffeomorph_toUnits_mul_mul_toUnits`: unitary
  equivariance of the right polar coordinates, with the one-sided cases
  `Matrix.GeneralLinearGroup.rightPolarDiffeomorph_toUnits_mul` and
  `Matrix.GeneralLinearGroup.coe_rightPolarDiffeomorph_mul_toUnits_snd`.
* `Matrix.GeneralLinearGroup.det_eq_one_iff_polarDiffeomorph`: the determinant-one condition in
  polar coordinates.
* `Matrix.SpecialLinearGroup.polarDiffeomorph`, `Matrix.SpecialLinearGroup.rightPolarDiffeomorph`:
  the polar and right polar coordinates on `SL(n, 𝕜)`, with `polarDiffeomorph_eq_iff` and
  `rightPolarDiffeomorph_eq_iff` characterizing them as the unique factorizations.
* `Matrix.SpecialLinearGroup.polarDiffeomorph_toSL_mul_mul_toSL`,
  `Matrix.SpecialLinearGroup.rightPolarDiffeomorph_toSL_mul_mul_toSL`: special unitary
  equivariance of the polar coordinates on `SL(n, 𝕜)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1.
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
  invFun p := ((mem_posDefOpens _).1 p.1.property).isUnit.unit * Unitary.toUnits p.2
  left_inv A := Units.ext (Units.sqrt_mul_star_mul_polarUnitary A)
  right_inv p := by
    have hp := ((mem_posDefOpens _).1 p.1.property).posSemidef.nonneg
    have h : ((((mem_posDefOpens _).1 p.1.property).isUnit.unit * Unitary.toUnits p.2 : GL n 𝕜) :
        Matrix n n 𝕜) = (p.1.val : Matrix n n 𝕜) * p.2 := by
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
      contMDiff_coe_posDefOpens.comp contMDiff_fst
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

/-- **Unitary equivariance of the polar coordinates.** For unitary matrices `V` and `W`, the polar
coordinates of `V A W` are `(V P Vᴴ, V U W)`, where `(P, U)` are the polar coordinates of `A`. -/
theorem polarDiffeomorph_toUnits_mul_mul_toUnits (V : unitaryGroup n 𝕜) (A : GL n 𝕜)
    (W : unitaryGroup n 𝕜) :
    polarDiffeomorph n 𝕜 (Unitary.toUnits V * A * Unitary.toUnits W) =
      (posDefUnitaryConj n 𝕜 ∞ V (polarDiffeomorph n 𝕜 A).1,
        V * (polarDiffeomorph n 𝕜 A).2 * W) := by
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Units.polarUnitary_unitary_mul_mul_unitary A V W)
  rw [coe_posDefUnitaryConj_apply, coe_polarDiffeomorph_apply_fst, coe_polarDiffeomorph_apply_fst]
  exact Units.sqrt_unitary_mul_mul_unitary A V W

/-- Left multiplication by a unitary matrix `V` conjugates the positive polar coordinate by `V`
and multiplies the unitary polar coordinate on the left. -/
theorem polarDiffeomorph_toUnits_mul (V : unitaryGroup n 𝕜) (A : GL n 𝕜) :
    polarDiffeomorph n 𝕜 (Unitary.toUnits V * A) =
      (posDefUnitaryConj n 𝕜 ∞ V (polarDiffeomorph n 𝕜 A).1, V * (polarDiffeomorph n 𝕜 A).2) := by
  simpa using polarDiffeomorph_toUnits_mul_mul_toUnits V A 1

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

/-! ### The right polar coordinates `A = U Q` -/

variable (n 𝕜) in
/-- **Right polar coordinates on `GL(n, 𝕜)`** for `𝕜 = ℝ` or `ℂ`: the global real smooth
diffeomorphism `A ↦ (U, √(Aᴴ A))` from the invertible matrices onto the product of the unitary
group (the orthogonal group when `𝕜 = ℝ`) and the positive-definite cone, whose inverse is
`(U, Q) ↦ U Q`. The unitary coordinate `U` is the same as for `polarDiffeomorph`.

It is the inverse Cartan diffeomorphism `A ↦ (U, X)` followed by the exponential coordinates
`X ↦ exp X` of the cone. To use this diffeomorphism, open the `Matrix.Norms.L2Operator` scope and
enable `Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def rightPolarDiffeomorph : GL n 𝕜 ≃ₘ^∞⟮𝓘(ℝ, Matrix n n 𝕜),
    (Unitary.model (Matrix n n 𝕜)).prod 𝓘(ℝ, selfAdjoint (Matrix n n 𝕜))⟯
    unitaryGroup n 𝕜 × posDefOpens n 𝕜 :=
  (cartanDiffeomorph n 𝕜).symm.trans
    ((Diffeomorph.refl _ _ _).prodCongr (hermitianExpDiffeomorph n 𝕜 ∞))

/-- The unitary coordinate of the right polar diffeomorphism is the unitary polar factor. -/
@[simp]
theorem rightPolarDiffeomorph_apply_fst (A : GL n 𝕜) :
    (rightPolarDiffeomorph n 𝕜 A).1 = A.polarUnitary :=
  cartanDiffeomorph_symm_apply_fst A

/-- The positive coordinate of the right polar diffeomorphism is the right positive factor
`√(Aᴴ A)`. -/
@[simp]
theorem coe_rightPolarDiffeomorph_apply_snd (A : GL n 𝕜) :
    (((rightPolarDiffeomorph n 𝕜 A).2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      CFC.sqrt (star (A : Matrix n n 𝕜) * A) := by
  have hpos : (CFC.sqrt (star (A : Matrix n n 𝕜) * A)).PosDef := by
    simpa using posDef_sqrt_mul_star (star A)
  calc _ = NormedSpace.exp ((((cartanDiffeomorph n 𝕜).symm A).2 :
          selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) :=
        coe_hermitianExpDiffeomorph_apply ∞ _
    _ = _ := by rw [coe_cartanDiffeomorph_symm_apply_snd, hpos.exp_cfc_log]

/-- The inverse right polar diffeomorphism multiplies the two coordinates. -/
@[simp]
theorem coe_rightPolarDiffeomorph_symm_apply (p : unitaryGroup n 𝕜 × posDefOpens n 𝕜) :
    ((rightPolarDiffeomorph n 𝕜).symm p : Matrix n n 𝕜) =
      (p.1 : Matrix n n 𝕜) * ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) := by
  obtain ⟨A, rfl⟩ := (rightPolarDiffeomorph n 𝕜).surjective p
  rw [Diffeomorph.coe_toEquiv, Diffeomorph.symm_apply_apply, rightPolarDiffeomorph_apply_fst,
    coe_rightPolarDiffeomorph_apply_snd, Units.polarUnitary_mul_sqrt_star_mul]

/-- The right polar coordinates are the unique factorization of `A` as a unitary matrix times a
positive-definite matrix: a pair from the unitary group and the cone is the right polar
coordinate pair of `A` exactly when its product is `A`. -/
theorem rightPolarDiffeomorph_eq_iff (A : GL n 𝕜) (p : unitaryGroup n 𝕜 × posDefOpens n 𝕜) :
    rightPolarDiffeomorph n 𝕜 A = p ↔
      (p.1 : Matrix n n 𝕜) * ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) = A := by
  rw [← coe_rightPolarDiffeomorph_symm_apply, ← Units.ext_iff]
  constructor
  · rintro rfl
    exact (rightPolarDiffeomorph n 𝕜).symm_apply_apply A
  · rintro rfl
    exact (rightPolarDiffeomorph n 𝕜).apply_symm_apply p

/-- The right positive coordinate `√(Aᴴ A)` is the left positive coordinate `√(A Aᴴ)` conjugated
by the common unitary coordinate: `Q = Uᴴ P U`, so that `A = P U = U (Uᴴ P U)`. -/
theorem coe_rightPolarDiffeomorph_apply_snd_eq_star_mul_mul (A : GL n 𝕜) :
    (((rightPolarDiffeomorph n 𝕜 A).2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) =
      star ((polarDiffeomorph n 𝕜 A).2 : Matrix n n 𝕜) *
        (((polarDiffeomorph n 𝕜 A).1 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
          ((polarDiffeomorph n 𝕜 A).2 : Matrix n n 𝕜) := by
  rw [coe_rightPolarDiffeomorph_apply_snd, coe_polarDiffeomorph_apply_fst,
    polarDiffeomorph_apply_snd]
  exact Units.sqrt_star_mul_eq A

/-- Left multiplication by a unitary matrix fixes the positive right polar coordinate and
multiplies the unitary coordinate on the left. -/
theorem rightPolarDiffeomorph_toUnits_mul (V : unitaryGroup n 𝕜) (A : GL n 𝕜) :
    rightPolarDiffeomorph n 𝕜 (Unitary.toUnits V * A) =
      (V * (rightPolarDiffeomorph n 𝕜 A).1, (rightPolarDiffeomorph n 𝕜 A).2) := by
  rw [rightPolarDiffeomorph_eq_iff, coe_rightPolarDiffeomorph_apply_snd,
    rightPolarDiffeomorph_apply_fst, Submonoid.coe_mul, mul_assoc,
    Units.polarUnitary_mul_sqrt_star_mul, Units.val_mul, Unitary.val_toUnits_apply]

/-- Right multiplication by a unitary matrix `W` conjugates the positive right polar coordinate:
the right positive factor of `A W` is `Wᴴ Q W`, where `Q` is the right positive factor of `A`. -/
theorem coe_rightPolarDiffeomorph_mul_toUnits_snd (A : GL n 𝕜) (W : unitaryGroup n 𝕜) :
    (((rightPolarDiffeomorph n 𝕜 (A * Unitary.toUnits W)).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      star (W : Matrix n n 𝕜) *
        (((rightPolarDiffeomorph n 𝕜 A).2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
          (W : Matrix n n 𝕜) := by
  rw [coe_rightPolarDiffeomorph_apply_snd, coe_rightPolarDiffeomorph_apply_snd, Units.val_mul,
    Unitary.val_toUnits_apply, star_mul, mul_assoc, ← mul_assoc (star (A : Matrix n n 𝕜)),
    ← mul_assoc]
  simpa only [Unitary.coe_star, star_star] using
    CFC.sqrt_unitary_mul_mul_star (star W) (star (A : Matrix n n 𝕜) * A)

/-- **Unitary equivariance of the right polar coordinates.** For unitary matrices `V` and `W`, the
right polar coordinates of `V A W` are `(V U W, Wᴴ Q W)`, where `(U, Q)` are the right polar
coordinates of `A`. -/
theorem rightPolarDiffeomorph_toUnits_mul_mul_toUnits (V : unitaryGroup n 𝕜) (A : GL n 𝕜)
    (W : unitaryGroup n 𝕜) :
    rightPolarDiffeomorph n 𝕜 (Unitary.toUnits V * A * Unitary.toUnits W) =
      (V * (rightPolarDiffeomorph n 𝕜 A).1 * W,
        posDefUnitaryConj n 𝕜 ∞ (star W) (rightPolarDiffeomorph n 𝕜 A).2) := by
  rw [mul_assoc, rightPolarDiffeomorph_toUnits_mul]
  refine Prod.ext ?_ (Subtype.ext (Subtype.ext ?_))
  · rw [rightPolarDiffeomorph_apply_fst, rightPolarDiffeomorph_apply_fst, mul_assoc]
    simpa using congrArg (V * ·) (Units.polarUnitary_unitary_mul_mul_unitary A 1 W)
  · rw [coe_rightPolarDiffeomorph_mul_toUnits_snd, coe_posDefUnitaryConj_apply, Unitary.coe_star,
      star_star]

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
diffeomorphism `Matrix.GeneralLinearGroup.polarDiffeomorph` is a global real smooth
diffeomorphism `A ↦ (√(A Aᴴ), U)` from the special linear group onto the product of the
positive-definite matrices of determinant one with the special unitary group (the special
orthogonal group when `𝕜 = ℝ`). Its inverse is `(P, U) ↦ P U`.

The special linear group carries the real structure of its native analytic atlas, the
positive-definite matrices of determinant one their regular-level structure
(`Matrix.PosDefDetOne.instChartedSpace`), and the special unitary group its native Lie-group
structure (`Matrix.specialUnitaryGroup.instChartedSpace`). To use this diffeomorphism, open the
`Matrix.Norms.L2Operator` scope and enable `Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def polarDiffeomorph : SpecialLinearGroup n 𝕜 ≃ₘ^∞⟮𝓘(ℝ, Model n 𝕜),
    𝓘(ℝ, PosDefDetOne.Model n 𝕜).prod (specialUnitaryGroup.model n 𝕜)⟯
    PosDefDetOne n 𝕜 × specialUnitaryGroup n 𝕜 where
  toFun g :=
    have h := (det_eq_one_iff_polarDiffeomorph (toGL g)).1 g.property
    (⟨(GeneralLinearGroup.polarDiffeomorph n 𝕜 (toGL g)).1, h.1⟩,
      ⟨(GeneralLinearGroup.polarDiffeomorph n 𝕜 (toGL g)).2,
        mem_specialUnitaryGroup_iff.2
          ⟨(GeneralLinearGroup.polarDiffeomorph n 𝕜 (toGL g)).2.property, h.2⟩⟩)
  invFun p := ⟨((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) * (p.2 : Matrix n n 𝕜), by
    rw [det_mul, p.1.property, (mem_specialUnitaryGroup_iff.1 p.2.property).2, mul_one]⟩
  left_inv g := Subtype.ext (Units.sqrt_mul_star_mul_polarUnitary (toGL g))
  right_inv := by
    rintro ⟨⟨P, hP⟩, U, hU⟩
    have h := (GeneralLinearGroup.polarDiffeomorph_eq_iff
      (toGL ⟨((P : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) * (U : Matrix n n 𝕜),
        by rw [det_mul, hP, (mem_specialUnitaryGroup_iff.1 hU).2, mul_one]⟩)
      (P, ⟨U, (mem_specialUnitaryGroup_iff.1 hU).1⟩)).2 rfl
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg (fun q ↦ (q.2 : Matrix n n 𝕜)) h))
  contMDiff_toFun := by
    have h := (GeneralLinearGroup.polarDiffeomorph n 𝕜).contMDiff.comp contMDiff_toGL_real
    refine ContMDiff.prodMk ?_ ?_
    · exact PosDefDetOne.contMDiff_subtypeVal_comp_iff.1 (contMDiff_fst.comp h)
    · exact specialUnitaryGroup.contMDiff_iff.2
        (Unitary.contMDiff_val.comp (contMDiff_snd.comp h))
  contMDiff_invFun := by
    refine isSmoothEmbedding_subtypeVal_real.contMDiff_iff_comp.2 ?_
    have hP : ContMDiff (𝓘(ℝ, PosDefDetOne.Model n 𝕜).prod (specialUnitaryGroup.model n 𝕜))
        𝓘(ℝ, Matrix n n 𝕜) ∞ (fun p : PosDefDetOne n 𝕜 × specialUnitaryGroup n 𝕜 ↦
          ((p.1.val : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜)) :=
      PosDefDetOne.contMDiff_coe.comp contMDiff_fst
    have hU : ContMDiff (𝓘(ℝ, PosDefDetOne.Model n 𝕜).prod (specialUnitaryGroup.model n 𝕜))
        𝓘(ℝ, Matrix n n 𝕜) ∞ (fun p : PosDefDetOne n 𝕜 × specialUnitaryGroup n 𝕜 ↦
          ((p.2 : specialUnitaryGroup n 𝕜) : Matrix n n 𝕜)) :=
      specialUnitaryGroup.contMDiff_val.comp contMDiff_snd
    exact (contDiff_mul.comp_contMDiff (hP.prodMk_space hU)).congr fun _ ↦ rfl

/-- The positive-definite coordinate of the polar coordinates on `SL(n, 𝕜)` is `√(A Aᴴ)`. -/
@[simp]
theorem coe_polarDiffeomorph_apply_fst (g : SpecialLinearGroup n 𝕜) :
    ((((polarDiffeomorph n 𝕜 g).1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) = CFC.sqrt ((g : Matrix n n 𝕜) * star (g : Matrix n n 𝕜)) := (rfl)

/-- The special unitary coordinate of the polar coordinates on `SL(n, 𝕜)` is the unitary polar
factor. -/
@[simp]
theorem coe_polarDiffeomorph_apply_snd (g : SpecialLinearGroup n 𝕜) :
    ((polarDiffeomorph n 𝕜 g).2 : Matrix n n 𝕜) = (toGL g).polarUnitary := (rfl)

/-- The inverse polar coordinates on `SL(n, 𝕜)` multiply the two coordinates. -/
@[simp]
theorem coe_polarDiffeomorph_symm_apply (p : PosDefDetOne n 𝕜 × specialUnitaryGroup n 𝕜) :
    ((polarDiffeomorph n 𝕜).symm p : Matrix n n 𝕜) =
      (((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
        (p.2 : Matrix n n 𝕜) := (rfl)

/-- The polar coordinates on `SL(n, 𝕜)` are the unique factorization of `g` as a
positive-definite matrix of determinant one times a special unitary matrix. -/
theorem polarDiffeomorph_eq_iff (g : SpecialLinearGroup n 𝕜)
    (p : PosDefDetOne n 𝕜 × specialUnitaryGroup n 𝕜) :
    polarDiffeomorph n 𝕜 g = p ↔
      (((p.1 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) *
        (p.2 : Matrix n n 𝕜) = g := by
  rw [← coe_polarDiffeomorph_symm_apply]
  constructor
  · rintro rfl
    rw [Diffeomorph.symm_apply_apply]
  · intro h
    rw [← Subtype.ext h, Diffeomorph.apply_symm_apply]

/-- **Special unitary equivariance of the polar coordinates on `SL(n, 𝕜)`.** For special unitary
matrices `V` and `W`, the polar coordinates of `V g W` are `(V P Vᴴ, V U W)`, where `(P, U)` are
the polar coordinates of `g`. -/
theorem polarDiffeomorph_toSL_mul_mul_toSL (V : specialUnitaryGroup n 𝕜)
    (g : SpecialLinearGroup n 𝕜) (W : specialUnitaryGroup n 𝕜) :
    polarDiffeomorph n 𝕜 (specialUnitaryGroup.toSL V * g * specialUnitaryGroup.toSL W) =
      (PosDefDetOne.unitaryConj n 𝕜 ∞ (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup V)
        (polarDiffeomorph n 𝕜 g).1, V * (polarDiffeomorph n 𝕜 g).2 * W) := by
  have h := GeneralLinearGroup.polarDiffeomorph_toUnits_mul_mul_toUnits
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup V) (toGL g)
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup W)
  rw [← specialUnitaryGroup.toGL_toSL, ← specialUnitaryGroup.toGL_toSL, ← map_mul,
    ← map_mul] at h
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext (congrArg (fun q ↦ (q.2 : Matrix n n 𝕜)) h))
  rw [PosDefDetOne.coe_unitaryConj_apply]
  exact congrArg Prod.fst h

/-! ### The right polar coordinates on `SL(n, 𝕜)` -/

variable (n 𝕜) in
/-- **Right polar coordinates on `SL(n, 𝕜)`** for `𝕜 = ℝ` or `ℂ`: the restriction of the right
polar diffeomorphism `Matrix.GeneralLinearGroup.rightPolarDiffeomorph` is a global real smooth
diffeomorphism `A ↦ (U, √(Aᴴ A))` from the special linear group onto the product of the special
unitary group (the special orthogonal group when `𝕜 = ℝ`) with the positive-definite matrices of
determinant one. Its inverse is `(U, Q) ↦ U Q`, and its special unitary coordinate `U` is that of
`Matrix.SpecialLinearGroup.polarDiffeomorph`.

To use this diffeomorphism, open the `Matrix.Norms.L2Operator` scope and enable
`Matrix.l2OpNormedAlgebraReal` as a local instance. -/
def rightPolarDiffeomorph : SpecialLinearGroup n 𝕜 ≃ₘ^∞⟮𝓘(ℝ, Model n 𝕜),
    (specialUnitaryGroup.model n 𝕜).prod 𝓘(ℝ, PosDefDetOne.Model n 𝕜)⟯
    specialUnitaryGroup n 𝕜 × PosDefDetOne n 𝕜 where
  toFun g :=
    (⟨(GeneralLinearGroup.rightPolarDiffeomorph n 𝕜 (toGL g)).1, mem_specialUnitaryGroup_iff.2
        ⟨(GeneralLinearGroup.rightPolarDiffeomorph n 𝕜 (toGL g)).1.property, by
          rw [GeneralLinearGroup.rightPolarDiffeomorph_apply_fst]
          exact det_polarUnitary_of_det_eq_one (toGL g) g.property⟩⟩,
      ⟨(GeneralLinearGroup.rightPolarDiffeomorph n 𝕜 (toGL g)).2, by
        rw [GeneralLinearGroup.coe_rightPolarDiffeomorph_apply_snd]
        exact (det_sqrt_star_mul (g : Matrix n n 𝕜)).trans (by
          rw [g.property, norm_one, RCLike.ofReal_one])⟩)
  invFun p := ⟨(p.1 : Matrix n n 𝕜) * ((p.2 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)), by
    rw [det_mul, p.2.property, (mem_specialUnitaryGroup_iff.1 p.1.property).2, mul_one]⟩
  left_inv g := Subtype.ext ((GeneralLinearGroup.coe_rightPolarDiffeomorph_symm_apply _).symm.trans
    (congrArg Units.val ((GeneralLinearGroup.rightPolarDiffeomorph n 𝕜).symm_apply_apply (toGL g))))
  right_inv := by
    rintro ⟨⟨U, hU⟩, ⟨Q, hQ⟩⟩
    have h := (GeneralLinearGroup.rightPolarDiffeomorph_eq_iff
      (toGL ⟨(U : Matrix n n 𝕜) * ((Q : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜),
        by rw [det_mul, hQ, (mem_specialUnitaryGroup_iff.1 hU).2, mul_one]⟩)
      (⟨U, (mem_specialUnitaryGroup_iff.1 hU).1⟩, Q)).2 rfl
    exact Prod.ext (Subtype.ext (congrArg (fun q ↦ (q.1 : Matrix n n 𝕜)) h))
      (Subtype.ext (congrArg Prod.snd h))
  contMDiff_toFun := by
    have h := (GeneralLinearGroup.rightPolarDiffeomorph n 𝕜).contMDiff.comp contMDiff_toGL_real
    refine ContMDiff.prodMk ?_ ?_
    · exact specialUnitaryGroup.contMDiff_iff.2
        (Unitary.contMDiff_val.comp (contMDiff_fst.comp h))
    · exact PosDefDetOne.contMDiff_subtypeVal_comp_iff.1 (contMDiff_snd.comp h)
  contMDiff_invFun := by
    refine isSmoothEmbedding_subtypeVal_real.contMDiff_iff_comp.2 ?_
    have hU : ContMDiff ((specialUnitaryGroup.model n 𝕜).prod 𝓘(ℝ, PosDefDetOne.Model n 𝕜))
        𝓘(ℝ, Matrix n n 𝕜) ∞ (fun p : specialUnitaryGroup n 𝕜 × PosDefDetOne n 𝕜 ↦
          ((p.1 : specialUnitaryGroup n 𝕜) : Matrix n n 𝕜)) :=
      specialUnitaryGroup.contMDiff_val.comp contMDiff_fst
    have hQ : ContMDiff ((specialUnitaryGroup.model n 𝕜).prod 𝓘(ℝ, PosDefDetOne.Model n 𝕜))
        𝓘(ℝ, Matrix n n 𝕜) ∞ (fun p : specialUnitaryGroup n 𝕜 × PosDefDetOne n 𝕜 ↦
          ((p.2.val : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜)) :=
      PosDefDetOne.contMDiff_coe.comp contMDiff_snd
    exact (contDiff_mul.comp_contMDiff (hU.prodMk_space hQ)).congr fun _ ↦ rfl

/-- The special unitary coordinate of the right polar coordinates on `SL(n, 𝕜)` is the unitary
polar factor. -/
@[simp]
theorem coe_rightPolarDiffeomorph_apply_fst (g : SpecialLinearGroup n 𝕜) :
    ((rightPolarDiffeomorph n 𝕜 g).1 : Matrix n n 𝕜) = (toGL g).polarUnitary :=
  congrArg Subtype.val (GeneralLinearGroup.rightPolarDiffeomorph_apply_fst (toGL g))

/-- The positive-definite coordinate of the right polar coordinates on `SL(n, 𝕜)` is the right
positive factor `√(Aᴴ A)`. -/
@[simp]
theorem coe_rightPolarDiffeomorph_apply_snd (g : SpecialLinearGroup n 𝕜) :
    ((((rightPolarDiffeomorph n 𝕜 g).2 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) = CFC.sqrt (star (g : Matrix n n 𝕜) * g) :=
  GeneralLinearGroup.coe_rightPolarDiffeomorph_apply_snd (toGL g)

/-- The inverse right polar coordinates on `SL(n, 𝕜)` multiply the two coordinates. -/
@[simp]
theorem coe_rightPolarDiffeomorph_symm_apply (p : specialUnitaryGroup n 𝕜 × PosDefDetOne n 𝕜) :
    ((rightPolarDiffeomorph n 𝕜).symm p : Matrix n n 𝕜) =
      (p.1 : Matrix n n 𝕜) * (((p.2 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) := (rfl)

/-- The right polar coordinates on `SL(n, 𝕜)` are the unique factorization of `g` as a special
unitary matrix times a positive-definite matrix of determinant one. -/
theorem rightPolarDiffeomorph_eq_iff (g : SpecialLinearGroup n 𝕜)
    (p : specialUnitaryGroup n 𝕜 × PosDefDetOne n 𝕜) :
    rightPolarDiffeomorph n 𝕜 g = p ↔
      (p.1 : Matrix n n 𝕜) * (((p.2 : posDefOpens n 𝕜) : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) = g := by
  rw [← coe_rightPolarDiffeomorph_symm_apply]
  constructor
  · rintro rfl
    rw [Diffeomorph.symm_apply_apply]
  · intro h
    rw [← Subtype.ext h, Diffeomorph.apply_symm_apply]

/-- **Special unitary equivariance of the right polar coordinates on `SL(n, 𝕜)`.** For special
unitary matrices `V` and `W`, the right polar coordinates of `V g W` are `(V U W, Wᴴ Q W)`, where
`(U, Q)` are the right polar coordinates of `g`. -/
theorem rightPolarDiffeomorph_toSL_mul_mul_toSL (V : specialUnitaryGroup n 𝕜)
    (g : SpecialLinearGroup n 𝕜) (W : specialUnitaryGroup n 𝕜) :
    rightPolarDiffeomorph n 𝕜 (specialUnitaryGroup.toSL V * g * specialUnitaryGroup.toSL W) =
      (V * (rightPolarDiffeomorph n 𝕜 g).1 * W, PosDefDetOne.unitaryConj n 𝕜 ∞
        (star (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup W))
        (rightPolarDiffeomorph n 𝕜 g).2) := by
  have h := GeneralLinearGroup.rightPolarDiffeomorph_toUnits_mul_mul_toUnits
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup V) (toGL g)
    (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup W)
  rw [← specialUnitaryGroup.toGL_toSL, ← specialUnitaryGroup.toGL_toSL, ← map_mul,
    ← map_mul] at h
  refine Prod.ext (Subtype.ext (congrArg (fun q ↦ (q.1 : Matrix n n 𝕜)) h)) (Subtype.ext ?_)
  rw [PosDefDetOne.coe_unitaryConj_apply]
  exact congrArg Prod.snd h

end Matrix.SpecialLinearGroup
