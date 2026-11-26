/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.LinearAlgebra.SesquilinearForm.IsometryGroup

/-!
# Isometric unitary actions on matrix Hom spaces

For Gram matrices `S` and `T`, the source and target unitary groups act on rectangular
matrices by `X ↦ h * X * g⁻¹`. With row-first coordinates `(i, j) ↦ X i j`, the Gram
matrix of the Hom pairing is `T ⊗ₖ S⁻¹ᵀ`. This file constructs the pairing-preserving
action and identifies matrix unitary groups with native sesquilinear isometry groups.

The pairing is `trace (Xᴴ * T * Y * S⁻¹)`. When `S` is invertible it is the usual Hom
pairing; the identities also hold for singular `S`, using Mathlib's total matrix inverse.
No Hermitian symmetry is required for the calculation. For signed Hermitian inputs,
dualizing the source gives the inverse-transposed Gram matrix. For two Hermitian inputs
the Hom pairing is Hermitian; multiplying one input pairing by a trace-zero scalar gives
the opposite-sign convention used to form a trace-symplectic tensor space. The trace
transfer and any metaplectic splitting are separate constructions.

## Provenance

`Matrix.unitaryGroupOf.homAction` is adapted from `New.U.kroneckerHom` (file
`src/Lib/Weil/DualPair/Kronecker.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
The extension to arbitrary Gram matrices over commutative star rings, the native
isometry-group comparison, and the evaluation and trace-pairing API are new here. The coordinate
interpretation follows `New.Space.hom` in `src/Lib/Weil/DualPair/Defs.lean`.

## References

* W. T. Gan and A. Ichino, *The Gross–Prasad conjecture and local theta correspondence*,
  §4.1, https://arxiv.org/pdf/1409.6824v2, p. 12, for the unitary tensor-pair convention.
-/

public section

open scoped Kronecker

namespace Matrix

variable {R n m : Type*} [CommRing R] [StarRing R]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

namespace unitaryGroupOf

/-- Matrix unitary isometries are exactly native isometries of the coordinate form. -/
theorem generalLinearEquiv_toLin_mem_isometryGroup_iff (S : Matrix n n R) (g : GL n R) :
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R))
      (GeneralLinearGroup.toLin g)) ∈
        (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) S).isometryGroup ↔
      g ∈ unitaryGroupOf S := by
  rw [LinearMap.mem_isometryGroup_iff, mem_unitaryGroupOf_iff_forall_dotProduct]
  simp only [toLinearMapₛₗ₂'_apply',
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.toLin_apply,
    mulVecLin_apply]
  -- The pointwise star and the function obtained by composing with star have the same values.
  rfl

/-- The matrix and native sesquilinear isometry groups of a Gram matrix are isomorphic. -/
noncomputable def isometryGroupEquiv (S : Matrix n n R) :
    unitaryGroupOf S ≃*
      (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) S).isometryGroup := by
  let e := GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R))
  refine (e.subgroupMap (unitaryGroupOf S)).trans (MulEquiv.subgroupCongr ?_)
  rw [Subgroup.map_equiv_eq_comap_symm]
  ext f
  exact (generalLinearEquiv_toLin_mem_isometryGroup_iff S (e.symm f)).symm.trans
    (by simp [e])

/-- The native isometry corresponding to a unitary matrix acts by matrix-vector multiplication. -/
@[simp]
theorem isometryGroupEquiv_apply (S : Matrix n n R) (g : unitaryGroupOf S) (x : n → R) :
    ((isometryGroupEquiv S g : (n → R) ≃ₗ[R] n → R) x) =
      ((g : GL n R) : Matrix n n R) *ᵥ x := (rfl)

/-- Recovering the unitary matrix of a native isometry gives its coordinate matrix. -/
@[simp]
theorem isometryGroupEquiv_symm_apply (S : Matrix n n R)
    (e : (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) S).isometryGroup) :
    (((isometryGroupEquiv S).symm e : GL n R) : Matrix n n R) =
      LinearMap.toMatrix' (e : (n → R) →ₗ[R] n → R) := by
  obtain ⟨g, rfl⟩ := (isometryGroupEquiv S).surjective e
  simp only [MulEquiv.symm_apply_apply]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [toLin'_apply, toLin'_toMatrix']
  exact (isometryGroupEquiv_apply S g x).symm

/-- The inverse-transpose source action preserves the dual Gram matrix. -/
theorem transpose_inv_mem_unitaryGroupOf_transpose_inv {S : Matrix n n R} (g : unitaryGroupOf S) :
    (GeneralLinearGroup.transposeMulEquiv n (g : GL n R)⁻¹).unop ∈
      unitaryGroupOf S⁻¹ᵀ := by
  rw [mem_unitaryGroupOf_iff, GeneralLinearGroup.coe_unop_transposeMulEquiv,
    GeneralLinearGroup.coe_inv, star_eq_conjTranspose, transpose_conjTranspose]
  have hg := congrArg (fun A : Matrix n n R ↦ A⁻¹) (mem_unitaryGroupOf_iff.mp g.property)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, star_eq_conjTranspose,
    ← conjTranspose_nonsing_inv, ← Matrix.mul_assoc] at hg
  calc
    (((g : GL n R) : Matrix n n R)⁻¹).map (starRingEnd R) * S⁻¹ᵀ *
        (((g : GL n R) : Matrix n n R)⁻¹)ᵀ =
        ((((g : GL n R) : Matrix n n R)⁻¹ * S⁻¹ *
          (((g : GL n R) : Matrix n n R)⁻¹)ᴴ))ᵀ := by
            simp only [transpose_mul, conjTranspose_transpose, Matrix.mul_assoc]
            rfl
    _ = S⁻¹ᵀ := congrArg transpose hg

variable (S : Matrix n n R) (T : Matrix m m R)

/-- The action `(g, h) ↦ h ⊗ₖ (g⁻¹)ᵀ`, preserving the Hom Gram matrix `T ⊗ₖ S⁻¹ᵀ`. -/
noncomputable def homAction :
    unitaryGroupOf S × unitaryGroupOf T →* unitaryGroupOf (T ⊗ₖ S⁻¹ᵀ) :=
  MonoidHom.mk'
    (fun p ↦ ⟨GeneralLinearGroup.kronecker (p.2 : GL m R)
      (GeneralLinearGroup.transposeMulEquiv n (p.1 : GL n R)⁻¹).unop, by
        rw [mem_unitaryGroupOf_iff]
        simp only [GeneralLinearGroup.kronecker, star_eq_conjTranspose,
          conjTranspose_kronecker, ← mul_kronecker_mul]
        rw [← star_eq_conjTranspose, ← star_eq_conjTranspose,
          mem_unitaryGroupOf_iff.mp p.2.property,
          mem_unitaryGroupOf_iff.mp (transpose_inv_mem_unitaryGroupOf_transpose_inv p.1)]⟩)
    (fun p q ↦ unitaryGroupOf.ext (by
      simp [GeneralLinearGroup.kronecker, ← mul_kronecker_mul]))

/-- The coordinate matrix of the Hom action is the indicated restricted Kronecker product. -/
@[simp]
theorem val_homAction (p : unitaryGroupOf S × unitaryGroupOf T) :
    ((homAction S T p : GL (m × n) R) : Matrix (m × n) (m × n) R) =
      ((p.2 : GL m R) : Matrix m m R) ⊗ₖ (((p.1 : GL n R)⁻¹ : GL n R) : Matrix n n R)ᵀ :=
  (rfl)

/-- On row-first matrix coordinates, the Hom action is `X ↦ h * X * g⁻¹`. -/
theorem homAction_mulVec_vec_transpose (p : unitaryGroupOf S × unitaryGroupOf T)
    (X : Matrix m n R) :
    ((homAction S T p : GL (m × n) R) : Matrix (m × n) (m × n) R) *ᵥ Xᵀ.vec =
      (((p.2 : GL m R) : Matrix m m R) * X *
        (((p.1 : GL n R)⁻¹ : GL n R) : Matrix n n R))ᵀ.vec := by
  rw [val_homAction, kronecker_mulVec_vec]
  simp only [transpose_mul, Matrix.mul_assoc]

/-- The source and target restrictions of the Hom action commute. -/
theorem commute_homAction (g : unitaryGroupOf S) (h : unitaryGroupOf T) :
    Commute (homAction S T (g, 1)) (homAction S T (1, h)) :=
  (MonoidHom.commute_inl_inr g h).map (homAction S T)

/-- The Hom action as a homomorphism between native sesquilinear isometry groups. -/
noncomputable def homIsometryAction :
    (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) S).isometryGroup ×
      (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) T).isometryGroup →*
        (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) (T ⊗ₖ S⁻¹ᵀ)).isometryGroup :=
  (isometryGroupEquiv (T ⊗ₖ S⁻¹ᵀ)).toMonoidHom.comp
    ((homAction S T).comp
      ((isometryGroupEquiv S).symm.prodCongr (isometryGroupEquiv T).symm).toMonoidHom)

/-- The native isometry action agrees with the matrix Hom action under the Gram comparisons. -/
@[simp]
theorem homIsometryAction_apply (g : unitaryGroupOf S) (h : unitaryGroupOf T) :
    homIsometryAction S T (isometryGroupEquiv S g, isometryGroupEquiv T h) =
      isometryGroupEquiv (T ⊗ₖ S⁻¹ᵀ) (homAction S T (g, h)) := by
  simp [homIsometryAction, MulEquiv.prodCongr]

/-- The source and target restrictions commute also in the native isometry group. -/
theorem commute_homIsometryAction
    (g : (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) S).isometryGroup)
    (h : (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) T).isometryGroup) :
    Commute (homIsometryAction S T (g, 1)) (homIsometryAction S T (1, h)) :=
  (MonoidHom.commute_inl_inr g h).map (homIsometryAction S T)

/-- The native isometry corresponding to the Hom action evaluates as `X ↦ h * X * g⁻¹`. -/
theorem homIsometryAction_apply_vec_transpose
    (e : (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) S).isometryGroup)
    (f : (toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) T).isometryGroup)
    (X : Matrix m n R) :
    ((homIsometryAction S T (e, f) : (m × n → R) ≃ₗ[R] m × n → R) Xᵀ.vec) =
      (LinearMap.toMatrix' (f : (m → R) →ₗ[R] m → R) * X *
        LinearMap.toMatrix' (e⁻¹).val.toLinearMap)ᵀ.vec := by
  rw [← isometryGroupEquiv_symm_apply T f,
    ← isometryGroupEquiv_symm_apply S (e⁻¹), map_inv]
  obtain ⟨g, rfl⟩ := (isometryGroupEquiv S).surjective e
  obtain ⟨h, rfl⟩ := (isometryGroupEquiv T).surjective f
  rw [homIsometryAction_apply, isometryGroupEquiv_apply, homAction_mulVec_vec_transpose,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  simp only [Subgroup.coe_inv]

/-- The Hom action preserves the sesquilinear pairing in row-first coordinates. -/
theorem star_vec_transpose_dotProduct_kronecker_mulVec_mul_mul_inv
    (p : unitaryGroupOf S × unitaryGroupOf T)
    (X Y : Matrix m n R) :
    star ((((p.2 : GL m R) : Matrix m m R) * X *
      (((p.1 : GL n R)⁻¹ : GL n R) : Matrix n n R))ᵀ.vec) ⬝ᵥ
        (T ⊗ₖ S⁻¹ᵀ) *ᵥ
          (((p.2 : GL m R) : Matrix m m R) * Y *
            (((p.1 : GL n R)⁻¹ : GL n R) : Matrix n n R))ᵀ.vec =
      star Xᵀ.vec ⬝ᵥ (T ⊗ₖ S⁻¹ᵀ) *ᵥ Yᵀ.vec := by
  simpa only [homAction_mulVec_vec_transpose] using
    (mem_unitaryGroupOf_iff_forall_dotProduct.mp (homAction S T p).property Xᵀ.vec Yᵀ.vec)

end unitaryGroupOf

omit [StarRing R] [DecidableEq m] in
/-- The Hom Gram matrix `T ⊗ₖ S⁻¹ᵀ` represents the pairing
`(X, Y) ↦ trace (Xᴴ * T * Y * S⁻¹)` in row-first coordinates. -/
theorem star_vec_transpose_dotProduct_kronecker_mulVec_vec_transpose [Star R]
    (S : Matrix n n R) (T : Matrix m m R)
    (X Y : Matrix m n R) :
    star Xᵀ.vec ⬝ᵥ (T ⊗ₖ S⁻¹ᵀ) *ᵥ Yᵀ.vec = (Xᴴ * T * Y * S⁻¹).trace := by
  rw [kronecker_mulVec_vec, star_vec_dotProduct_vec]
  rw [← trace_transpose]
  simp only [transpose_mul, transpose_transpose,
    ← conjTranspose_transpose_eq_transpose_conjTranspose]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

namespace unitaryGroupOf

/-- The trace pairing on matrix Hom spaces is invariant under `X ↦ h * X * g⁻¹`. -/
theorem trace_conjTranspose_mul_mul_mul_inv_conj_eq (S : Matrix n n R) (T : Matrix m m R)
    (g : unitaryGroupOf S) (h : unitaryGroupOf T) (X Y : Matrix m n R) :
    ((((h : GL m R) : Matrix m m R) * X *
      (((g : GL n R)⁻¹ : GL n R) : Matrix n n R))ᴴ * T *
        (((h : GL m R) : Matrix m m R) * Y *
          (((g : GL n R)⁻¹ : GL n R) : Matrix n n R)) * S⁻¹).trace =
      (Xᴴ * T * Y * S⁻¹).trace := by
  simpa only [star_vec_transpose_dotProduct_kronecker_mulVec_vec_transpose] using
    star_vec_transpose_dotProduct_kronecker_mulVec_mul_mul_inv S T (g, h) X Y

end unitaryGroupOf
end Matrix
