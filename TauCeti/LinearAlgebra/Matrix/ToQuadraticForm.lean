/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Basic rules for the quadratic form of a matrix

Elementary rules for Mathlib's `Matrix.toQuadraticForm'` — evaluation, its behaviour under
scaling, addition, negation, transposition and on diagonal matrices — together with the
isometries of the attached forms induced by congruence, block diagonals and reindexing. They are
kept apart from the signature theory so that consumers needing only these rules do not import it.

## Main definitions

* `Matrix.isometryEquivCongr`: congruence by a matrix with unit determinant is an isometry.
* `Matrix.isometryEquivFromBlocks`: a block-diagonal matrix gives the product of the forms.
* `Matrix.isometryEquivReindex`: reindexing transports the coordinates of the form.

## Main results

* `Matrix.toQuadraticForm'_apply`: the form evaluated at a vector is `x ⬝ᵥ A *ᵥ x`.
* `Matrix.toQuadraticForm'_smul`: scaling a matrix scales its quadratic form.
* `Matrix.toQuadraticForm'_add`: the quadratic form is additive in the matrix.
* `Matrix.toQuadraticForm'_transpose`: a matrix and its transpose carry the same form.
* `Matrix.toQuadraticForm'_add_transpose`: the form of `A + Aᵀ` is twice the form of `A`.
* `Matrix.toQuadraticForm'_diagonal`: a diagonal matrix gives a weighted sum of squares.
-/

public section

open QuadraticMap

namespace Matrix

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The quadratic form attached to a matrix, evaluated at a vector. -/
theorem toQuadraticForm'_apply (A : Matrix ι ι R) (x : ι → R) :
    A.toQuadraticForm' x = x ⬝ᵥ A *ᵥ x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

/-- Scaling a matrix scales its quadratic form. -/
@[simp]
theorem toQuadraticForm'_smul (c : R) (A : Matrix ι ι R) :
    (c • A).toQuadraticForm' = c • A.toQuadraticForm' := by
  simp [Matrix.toQuadraticForm']

/-- The quadratic form of a sum of matrices is the sum of their quadratic forms. -/
@[simp]
theorem toQuadraticForm'_add (A B : Matrix ι ι R) :
    (A + B).toQuadraticForm' = A.toQuadraticForm' + B.toQuadraticForm' := by
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_add]

/-- A matrix and its transpose carry the same quadratic form. -/
@[simp]
theorem toQuadraticForm'_transpose (A : Matrix ι ι R) :
    (Aᵀ).toQuadraticForm' = A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, toQuadraticForm'_apply, dotProduct_transpose_mulVec]

/-- The quadratic form of `A + Aᵀ` is twice the quadratic form of `A`. -/
theorem toQuadraticForm'_add_transpose (A : Matrix ι ι R) :
    (A + Aᵀ).toQuadraticForm' = (2 : R) • A.toQuadraticForm' := by
  rw [toQuadraticForm'_add, toQuadraticForm'_transpose, two_smul]

/-- The quadratic form of `-A` is the negative of the quadratic form of `A`. -/
@[simp]
theorem toQuadraticForm'_neg (A : Matrix ι ι R) :
    (-A).toQuadraticForm' = -A.toQuadraticForm' := by
  ext x
  simp [toQuadraticForm'_apply, neg_mulVec]

/-- The quadratic form of a diagonal matrix is the corresponding weighted sum of squares. -/
theorem toQuadraticForm'_diagonal (d : ι → R) :
    (diagonal d).toQuadraticForm' = weightedSumSquares R d := by
  ext x
  simp only [toQuadraticForm'_apply, weightedSumSquares_apply, dotProduct, mulVec_diagonal,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Congruence by a matrix with unit determinant is an isometry of the attached quadratic
forms. -/
noncomputable def isometryEquivCongr {P : Matrix ι ι R} (hP : IsUnit P.det) (A : Matrix ι ι R) :
    (P * A * Pᵀ).toQuadraticForm'.IsometryEquiv A.toQuadraticForm' where
  toLinearEquiv := Pᵀ.toLinearEquiv (Pi.basisFun R ι) (by rwa [det_transpose])
  map_app' x := by
    simp [toQuadraticForm'_apply, toLin_eq_toLin', ← mulVec_mulVec, dotProduct_mulVec,
      mulVec_transpose]

/-- Splitting the coordinates of a block-diagonal matrix is an isometry onto the orthogonal
product of the quadratic forms of the two blocks. -/
def isometryEquivFromBlocks (A : Matrix ι ι R) (B : Matrix κ κ R) :
    (fromBlocks A 0 0 B).toQuadraticForm'.IsometryEquiv
      (A.toQuadraticForm'.prod B.toQuadraticForm') where
  toLinearEquiv := LinearEquiv.sumArrowLequivProdArrow ι κ R R
  map_app' x := by
    obtain ⟨u, v, rfl⟩ : ∃ u v, Sum.elim u v = x := ⟨_, _, Sum.elim_comp_inl_inr x⟩
    have huv : LinearEquiv.sumArrowLequivProdArrow ι κ R R (Sum.elim u v) = (u, v) := by
      ext <;> simp
    simp [toQuadraticForm'_apply, huv, fromBlocks_mulVec, sumElim_dotProduct_sumElim]

/-- Reindexing the rows and columns of a matrix along the same equivalence only transports the
coordinates of its quadratic form. -/
def isometryEquivReindex (e : ι ≃ κ) (A : Matrix ι ι R) :
    (reindex e e A).toQuadraticForm'.IsometryEquiv A.toQuadraticForm' where
  toLinearEquiv := LinearEquiv.funCongrLeft R R e
  map_app' x := by
    have hx : LinearEquiv.funCongrLeft R R e x = x ∘ e := funext fun _ => by simp
    simp [toQuadraticForm'_apply, hx, submatrix_mulVec_equiv]

end Matrix
