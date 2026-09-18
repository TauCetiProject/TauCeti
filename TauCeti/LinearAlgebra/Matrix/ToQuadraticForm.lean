/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Basic rules for the quadratic form of a matrix

Elementary rules for Mathlib's `Matrix.toQuadraticForm'` — evaluation, its behaviour under
scaling, negation, transposition and on diagonal matrices — together with the isometries of the
attached forms induced by congruence, block diagonals and reindexing. They are kept apart from
the signature theory so that consumers needing only these rules do not import it.

## Main definitions

* `Matrix.isometryEquivCongr`: congruence by a matrix with unit determinant is an isometry.
* `Matrix.isometryEquivFromBlocks`: a block-diagonal matrix gives the product of the forms.
* `Matrix.isometryEquivReindex`: reindexing transports the coordinates of the form.

## Main results

* `Matrix.toQuadraticForm'_apply`: the form evaluated at a vector is `x ⬝ᵥ A *ᵥ x`.
* `Matrix.toQuadraticForm'_smul`: scaling a matrix scales its quadratic form.
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

/-- Reindexing the rows and columns of a matrix along the same equivalence only transports the
coordinates of its quadratic form. -/
def isometryEquivReindex (e : ι ≃ κ) (A : Matrix ι ι R) :
    (reindex e e A).toQuadraticForm'.IsometryEquiv A.toQuadraticForm' where
  toLinearEquiv := LinearEquiv.funCongrLeft R R e
  map_app' x := by
    rw [toQuadraticForm'_apply, toQuadraticForm'_apply, reindex_apply, submatrix_mulVec_equiv,
      ← comp_equiv_dotProduct_comp_equiv (e := e)]
    simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    rfl

end Matrix
