/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The signature of a square matrix over a linearly ordered field

The *signature* of a square matrix `A` over a linearly ordered field is the difference between
the two indices of inertia of the quadratic form `x ↦ x ⬝ᵥ A *ᵥ x`, that is Mathlib's
`sigPos A.toQuadraticForm' - sigNeg A.toQuadraticForm'`. Only the symmetric part of `A` is
visible to that form, so the signature of `A` agrees with the signature of `A + Aᵀ`.

The three properties that make the signature computable are proved here: it is invariant under
congruence `A ↦ P * A * Pᵀ` by a matrix with unit determinant, it is additive along a block
diagonal, and on a diagonal matrix it counts the positive entries against the negative ones.
Together these evaluate the signature of any matrix diagonalised by an explicit congruence.

For an integral symmetric bilinear form presented as a lattice,
`TauCeti.IntegralLattice.signature` records the finer triple `(n₊, n₀, n₋)`; the definition
here is the basis-level matrix counterpart, which is what a congruence class of matrices — such
as the S-equivalence class of a Seifert matrix — offers.

## Main definitions

* `Matrix.signature`: the difference of the two indices of inertia.

## Main results

* `Matrix.signature_congr`: invariance under congruence by a matrix with unit determinant.
* `Matrix.signature_fromBlocks_zero`: additivity along a block diagonal.
* `Matrix.signature_diagonal`: the signature of a diagonal matrix as a sum of signs.
* `Matrix.signature_hyperbolicGram`: the hyperbolic plane has signature zero.
* `Matrix.signature_eq_of_congr_diagonal`: the signature read off an explicit diagonalising
  congruence.
* `Matrix.signature_add_transpose`: the signature of `A + Aᵀ` is the signature of `A`.
* `Matrix.signature_smul_of_pos`: positive scaling does not change the signature.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Finset QuadraticMap

namespace Matrix

section CommRing

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The quadratic form attached to a matrix, evaluated at a vector. -/
theorem toQuadraticForm'_apply (A : Matrix ι ι R) (x : ι → R) :
    A.toQuadraticForm' x = x ⬝ᵥ A *ᵥ x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

-- Not a `simp` lemma: `TauCeti.PDE.toQuadraticForm'_transpose` already normalises the same
-- left-hand side pointwise on `EuclideanSpace ℝ n`, and the two cannot both be simp-normal.
/-- A matrix and its transpose carry the same quadratic form. -/
theorem toQuadraticForm'_transpose (A : Matrix ι ι R) :
    (Aᵀ).toQuadraticForm' = A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, toQuadraticForm'_apply, ← vecMul_transpose, transpose_transpose,
    dotProduct_comm, dotProduct_mulVec]

/-- The quadratic form of `A + Aᵀ` is twice the quadratic form of `A`. -/
theorem toQuadraticForm'_add_transpose (A : Matrix ι ι R) :
    (A + Aᵀ).toQuadraticForm' = (2 : R) • A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, _root_.smul_apply, smul_eq_mul, toQuadraticForm'_apply,
    add_mulVec, dotProduct_add, ← toQuadraticForm'_apply, ← toQuadraticForm'_apply,
    toQuadraticForm'_transpose]
  ring

-- Not a `simp` lemma, for the same reason as `toQuadraticForm'_transpose` above:
-- `TauCeti.PDE.toQuadraticForm'_smul` is already `simp` and normalises the same left-hand side
-- pointwise on `EuclideanSpace ℝ n`, so tagging this one makes that one non-simp-normal.
/-- Scaling a matrix scales its quadratic form. -/
theorem toQuadraticForm'_smul (c : R) (A : Matrix ι ι R) :
    (c • A).toQuadraticForm' = c • A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, _root_.smul_apply, smul_eq_mul, toQuadraticForm'_apply,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The quadratic form of `-A` is the negative of the quadratic form of `A`. -/
@[simp]
theorem toQuadraticForm'_neg (A : Matrix ι ι R) :
    (-A).toQuadraticForm' = -A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, _root_.neg_apply, toQuadraticForm'_apply, neg_mulVec,
    dotProduct_neg]

/-- The quadratic form of a diagonal matrix is the corresponding weighted sum of squares. -/
theorem toQuadraticForm'_diagonal (d : ι → R) :
    (diagonal d).toQuadraticForm' = weightedSumSquares R d := by
  ext x
  rw [toQuadraticForm'_apply, weightedSumSquares_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, smul_eq_mul]
  ring

/-- Congruence by a matrix with unit determinant is an isometry of the attached quadratic
forms. -/
noncomputable def isometryEquivCongr {P : Matrix ι ι R} (hP : IsUnit P.det) (A : Matrix ι ι R) :
    (P * A * Pᵀ).toQuadraticForm'.IsometryEquiv A.toQuadraticForm' where
  toLinearEquiv :=
    { toFun := fun x => Pᵀ *ᵥ x
      map_add' := fun x y => by rw [mulVec_add]
      map_smul' := fun c x => by rw [mulVec_smul, RingHom.id_apply]
      invFun := fun x => (Pᵀ)⁻¹ *ᵥ x
      left_inv := fun x => by
        dsimp only
        rw [mulVec_mulVec, nonsing_inv_mul _ (by rwa [det_transpose]), one_mulVec]
      right_inv := fun x => by
        dsimp only
        rw [mulVec_mulVec, mul_nonsing_inv _ (by rwa [det_transpose]), one_mulVec] }
  map_app' x := by
    have h₁ : (P * A * Pᵀ) *ᵥ x = P *ᵥ A *ᵥ Pᵀ *ᵥ x := by
      rw [mulVec_mulVec, mulVec_mulVec, mul_assoc]
    have h₂ : x ⬝ᵥ P *ᵥ A *ᵥ Pᵀ *ᵥ x = (x ᵥ* P) ⬝ᵥ A *ᵥ Pᵀ *ᵥ x := dotProduct_mulVec _ _ _
    dsimp only
    rw [toQuadraticForm'_apply, toQuadraticForm'_apply, h₁, h₂, mulVec_transpose]

/-- Splitting the coordinates of a block-diagonal matrix is an isometry onto the orthogonal
product of the quadratic forms of the two blocks. -/
def isometryEquivFromBlocks (A : Matrix ι ι R) (B : Matrix κ κ R) :
    (fromBlocks A 0 0 B).toQuadraticForm'.IsometryEquiv
      (A.toQuadraticForm'.prod B.toQuadraticForm') where
  toLinearEquiv :=
    { toFun := fun x => (fun i => x (Sum.inl i), fun j => x (Sum.inr j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p => Sum.elim p.1 p.2
      left_inv := fun x => funext fun p => by cases p <;> rfl
      right_inv := fun _ => rfl }
  map_app' x := by
    have hx : Sum.elim (fun i => x (Sum.inl i)) (fun j => x (Sum.inr j)) = x :=
      funext fun p => by cases p <;> rfl
    rw [QuadraticMap.prod_apply, toQuadraticForm'_apply, toQuadraticForm'_apply,
      toQuadraticForm'_apply, ← hx, fromBlocks_mulVec]
    simp [sumElim_dotProduct_sumElim]

end CommRing

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The signature of a square matrix over a linearly ordered field: the positive index of
inertia of the quadratic form `x ↦ x ⬝ᵥ A *ᵥ x` minus its negative index.

Only the symmetric part of `A` contributes, by `Matrix.signature_add_transpose`.

The quadratic form of a matrix does not depend on the decidability of equality on the index
type, so the local decider here is invisible: `Matrix.signature_def` identifies the definition
with the one read off any `DecidableEq ι` instance. Keeping it local leaves `DecidableEq` out
of the statements that do not mention `Matrix.toQuadraticForm'`, `Matrix.diagonal` or
`Matrix.det` themselves. -/
noncomputable def signature (A : Matrix ι ι 𝕜) : ℤ :=
  letI := Classical.decEq ι
  (_root_.sigPos A.toQuadraticForm' : ℤ) - (_root_.sigNeg A.toQuadraticForm' : ℤ)

theorem signature_def [DecidableEq ι] (A : Matrix ι ι 𝕜) :
    signature A =
      (_root_.sigPos A.toQuadraticForm' : ℤ) - (_root_.sigNeg A.toQuadraticForm' : ℤ) := by
  rw [signature, Subsingleton.elim (Classical.decEq ι) ‹DecidableEq ι›]

/-- Isometric quadratic forms have the same signature, so the signature only depends on the
isometry class of the form of a matrix. -/
theorem signature_eq_of_equivalent [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι 𝕜}
    {B : Matrix κ κ 𝕜} (h : A.toQuadraticForm'.Equivalent B.toQuadraticForm') :
    signature A = signature B := by
  rw [signature_def, signature_def, h.sigPos_eq, h.sigNeg_eq]

/-- **Congruence invariance of the signature.** Replacing `A` by `P * A * Pᵀ` for a matrix `P`
with unit determinant does not change the signature. -/
theorem signature_congr [DecidableEq ι] {P : Matrix ι ι 𝕜} (hP : IsUnit P.det)
    (A : Matrix ι ι 𝕜) : signature (P * A * Pᵀ) = signature A :=
  signature_eq_of_equivalent ⟨isometryEquivCongr hP A⟩

/-- Transposing a matrix does not change its signature. -/
@[simp]
theorem signature_transpose (A : Matrix ι ι 𝕜) : signature Aᵀ = signature A := by
  classical
  rw [signature_def, signature_def, toQuadraticForm'_transpose]

/-- Negating a matrix negates its signature. -/
@[simp]
theorem signature_neg (A : Matrix ι ι 𝕜) : signature (-A) = -signature A := by
  classical
  rw [signature_def, signature_def, toQuadraticForm'_neg, sigPos_neg, sigNeg_neg]
  ring

/-- The zero matrix has signature zero. -/
@[simp]
theorem signature_zero : signature (0 : Matrix ι ι 𝕜) = 0 := by
  have h := signature_neg (0 : Matrix ι ι 𝕜)
  simp only [neg_zero] at h
  omega

/-- A matrix indexed by an empty type has signature zero. -/
@[simp]
theorem signature_of_isEmpty [IsEmpty ι] (A : Matrix ι ι 𝕜) : signature A = 0 := by
  classical
  have h : Module.finrank 𝕜 (ι → 𝕜) = 0 := by simp
  have hpos := _root_.sigPos_le_finrank A.toQuadraticForm'
  have hneg := _root_.sigPos_le_finrank (-A.toQuadraticForm')
  rw [h] at hpos hneg
  rw [signature_def, ← sigPos_neg]
  omega

section StrictOrdered

variable [IsStrictOrderedRing 𝕜]

/-- The signature of a matrix is the signature of its symmetrisation `A + Aᵀ`. -/
@[simp]
theorem signature_add_transpose (A : Matrix ι ι 𝕜) : signature (A + Aᵀ) = signature A := by
  classical
  rw [signature_def, signature_def, toQuadraticForm'_add_transpose,
    QuadraticForm.sigPos_smul_of_pos _ two_pos, QuadraticForm.sigNeg_smul_of_pos _ two_pos]

/-- Scaling a matrix by a positive scalar does not change its signature. -/
@[simp]
theorem signature_smul_of_pos {c : 𝕜} (hc : 0 < c) (A : Matrix ι ι 𝕜) :
    signature (c • A) = signature A := by
  classical
  rw [signature_def, signature_def, toQuadraticForm'_smul,
    QuadraticForm.sigPos_smul_of_pos _ hc, QuadraticForm.sigNeg_smul_of_pos _ hc]

/-- **Additivity of the signature along a block diagonal.** -/
@[simp]
theorem signature_fromBlocks_zero (A : Matrix ι ι 𝕜) (B : Matrix κ κ 𝕜) :
    signature (fromBlocks A 0 0 B) = signature A + signature B := by
  classical
  have h : (fromBlocks A 0 0 B).toQuadraticForm'.Equivalent
      (A.toQuadraticForm'.prod B.toQuadraticForm') := ⟨isometryEquivFromBlocks A B⟩
  rw [signature_def, h.sigPos_eq, h.sigNeg_eq,
    QuadraticForm.sigPos_prod, QuadraticForm.sigNeg_prod, signature_def, signature_def]
  push_cast
  ring

/-- **The signature of a diagonal matrix** counts its positive entries against its negative
ones. -/
@[simp]
theorem signature_diagonal [DecidableEq ι] (d : ι → 𝕜) :
    signature (diagonal d) = ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 := by
  classical
  rw [signature_def, toQuadraticForm'_diagonal, QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
    Finset.card_filter, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter,
    Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases lt_trichotomy (d i) 0 with h | h | h
  · simp [h, asymm h]
  · simp [h]
  · simp [h, h.not_gt]

/-- **The signature from an explicit diagonalising congruence.** -/
theorem signature_eq_of_congr_diagonal [DecidableEq ι] {P A : Matrix ι ι 𝕜} (hP : IsUnit P.det)
    {d : ι → 𝕜} (h : P * A * Pᵀ = diagonal d) :
    signature A = ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 := by
  rw [← signature_congr hP A, h, signature_diagonal]

/-- The Gram matrix of a hyperbolic plane has signature zero: it is congruent to
`diagonal ![2, -2]`. -/
@[simp]
theorem signature_hyperbolicGram :
    signature (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) 𝕜) = 0 := by
  have hP : IsUnit (!![(1 : 𝕜), 1; 1, -1]).det := by
    rw [det_fin_two_of, isUnit_iff_ne_zero]
    norm_num
  have hd : !![(1 : 𝕜), 1; 1, -1] * !![0, 1; 1, 0] * (!![(1 : 𝕜), 1; 1, -1])ᵀ
      = diagonal ![2, -2] := by
    rw [diagonal_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, transpose_apply] <;> ring
  rw [signature_eq_of_congr_diagonal hP hd, Fin.sum_univ_two]
  norm_num

end StrictOrdered

end Matrix
