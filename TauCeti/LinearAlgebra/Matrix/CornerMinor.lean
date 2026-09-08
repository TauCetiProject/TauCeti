/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

/-!
# The corner minor of a doubly singular matrix

The *corner minor* of a square matrix `A` indexed by `Fin (n + 1)` is the determinant of the
submatrix obtained by deleting its last row and its last column, that is, the determinant of
`A.submatrix Fin.castSucc Fin.castSucc`. Unlike the determinant it is not a conjugation
invariant in general. It becomes one on a matrix that is annihilated on the right by a column
vector `u` and on the left by a row vector `w`, as soon as the conjugating matrix fixes `u` and
`w` as well and the last coordinates of `u` and `w` are units: this is
`Matrix.det_submatrix_castSucc_conj`.

The mechanism is that `u` and `w` give `A` a factorisation through the corner minor's own index
type `Fin n`: the identity with its last row replaced by `w` carries `A` into the image of the
inclusion `Fin n ↪ Fin (n + 1)`, and the identity with its last column replaced by `u` does the
same on the other side. A conjugation `A ↦ N * A * N⁻¹` by a matrix fixing `u` and `w` therefore
multiplies the corner minor by `N.det` on one side and by `N.det⁻¹` on the other.

The two Laplace expansions along the last row and the last column, in the sparse case used
throughout, are recorded first, together with the description of the corner minor as an ordinary
determinant after the last column is replaced by the last standard basis vector.

The intended source of such a matrix is `burau b - 1` for a braid `b`, where `u` is the all-ones
vector and `w` is the geometric vector `(1, t, …, t ^ n)`.

## Main results

* `Matrix.det_eq_mul_det_submatrix_castSucc_of_row` and
  `Matrix.det_eq_mul_det_submatrix_castSucc_of_col`: the determinant of a matrix whose last row,
  or whose last column, vanishes off the diagonal is the corner entry times the corner minor.
* `Matrix.det_updateCol_last_single`: replacing the last column by the last standard basis vector
  turns the determinant into the corner minor.
* `Matrix.submatrix_mul_of_mulVec_single`: deleting the last row and column commutes with a
  product when the left factor fixes the last standard basis vector.
* `Matrix.det_updateCol_last_smul_col_sub_single_of_det_sub_one_eq_zero`: a determinant formula
  for replacing the last column of `M - 1` by a linear combination of the last columns of `M`
  and `1`.
* `Matrix.det_submatrix_castSucc_conj`: the corner minor of `N * A * N⁻¹` equals that of `A`,
  when `A` is annihilated by `u` on the right and by `w` on the left and `N` fixes both.
-/

public section

namespace Matrix

variable {n : ℕ} {R : Type*}

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- Deleting the last row and column of a product is the product of the deletions, provided the
left factor has the last standard basis vector as its last column. -/
theorem submatrix_mul_of_mulVec_single (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hX : X *ᵥ Pi.single (Fin.last n) 1 = Pi.single (Fin.last n) 1) :
    (X * Y).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc * Y.submatrix Fin.castSucc Fin.castSucc := by
  have hcol : X.col (Fin.last n) = Pi.single (Fin.last n) 1 := by
    rw [← Matrix.mulVec_single_one]
    exact hX
  have hentry : ∀ i : Fin (n + 1),
      X i (Fin.last n) = (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) i :=
    fun i => congrFun hcol i
  ext u v
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hentry,
    Pi.single_eq_of_ne (Fin.castSucc_lt_last u).ne, zero_mul, add_zero]
  rfl

end NonAssocSemiring

variable [CommRing R]

/-- Laplace expansion along the last row of a matrix whose last row vanishes off the diagonal. -/
theorem det_eq_mul_det_submatrix_castSucc_of_row (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ j, j ≠ Fin.last n → A (Fin.last n) j = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last n),
    Finset.sum_eq_single (Fin.last n) (fun j _ hj => by rw [h j hj]; ring) (by simp)]
  rw [Fin.succAbove_last, Fin.val_last, Even.neg_one_pow ⟨n, rfl⟩, one_mul]

/-- Laplace expansion along the last column of a matrix whose last column vanishes off the
diagonal. -/
theorem det_eq_mul_det_submatrix_castSucc_of_col (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ i, i ≠ Fin.last n → A i (Fin.last n) = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← Matrix.det_transpose A, det_eq_mul_det_submatrix_castSucc_of_row Aᵀ h,
    Matrix.transpose_apply, ← Matrix.transpose_submatrix, Matrix.det_transpose]

/-- Replacing the last column of a matrix by the last standard basis vector turns its determinant
into its corner minor. -/
theorem det_updateCol_last_single (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (A.updateCol (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_eq_mul_det_submatrix_castSucc_of_col _ fun i hi => by
      rw [Matrix.updateCol_self, Pi.single_eq_of_ne hi],
    Matrix.updateCol_self, Pi.single_eq_same, one_mul]
  congr 1
  ext a b
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply,
    Matrix.updateCol_ne (Fin.castSucc_lt_last b).ne]

/-- The determinant of a matrix `M - 1` whose last column has been replaced by
`c • M.col (last) - e (last)`, in terms of the corner minor of `M - 1`. -/
theorem det_updateCol_last_smul_col_sub_single_of_det_sub_one_eq_zero
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hdet : (M - 1).det = 0) (c : R) :
    ((M - 1).updateCol (Fin.last n)
        (fun u => c * M u (Fin.last n) - (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) u)).det =
      (c - 1) * ((M - 1).submatrix Fin.castSucc Fin.castSucc).det := by
  have hfun : (fun u => c * M u (Fin.last n) - (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) u) =
      c • (fun u => (M - 1) u (Fin.last n)) +
        (c - 1) • (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) := by
    funext u
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply,
      Pi.single_apply]
    split_ifs <;> ring
  rw [hfun, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, Matrix.det_updateCol_smul,
    Matrix.updateCol_eq_self, hdet, Matrix.det_updateCol_last_single, mul_zero, zero_add]

/-! ### The two rectangular matrices that delete and restore the last coordinate -/

/-- The `n × (n + 1)` matrix that deletes the last coordinate. -/
private def projCastSucc (n : ℕ) (R : Type*) [CommRing R] : Matrix (Fin n) (Fin (n + 1)) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix Fin.castSucc id

/-- The `(n + 1) × n` matrix that includes the first `n` coordinates. -/
private def inclCastSucc (n : ℕ) (R : Type*) [CommRing R] : Matrix (Fin (n + 1)) (Fin n) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix id Fin.castSucc

private theorem projCastSucc_apply (a : Fin n) (b : Fin (n + 1)) :
    projCastSucc n R a b = if a.castSucc = b then 1 else 0 := by
  rw [projCastSucc, Matrix.submatrix_apply, Matrix.one_apply]
  rfl

private theorem inclCastSucc_apply (a : Fin (n + 1)) (b : Fin n) :
    inclCastSucc n R a b = if a = b.castSucc then 1 else 0 := by
  rw [inclCastSucc, Matrix.submatrix_apply, Matrix.one_apply]
  rfl

private theorem projCastSucc_mul {m : Type*} (A : Matrix (Fin (n + 1)) m R) :
    projCastSucc n R * A = A.submatrix Fin.castSucc id := by
  ext i k
  simp [Matrix.mul_apply, projCastSucc_apply, ite_mul]

private theorem mul_inclCastSucc {m : Type*} (A : Matrix m (Fin (n + 1)) R) :
    A * inclCastSucc n R = A.submatrix id Fin.castSucc := by
  ext i k
  simp [Matrix.mul_apply, inclCastSucc_apply, mul_ite]

private theorem projCastSucc_mul_mul_inclCastSucc (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    projCastSucc n R * A * inclCastSucc n R = A.submatrix Fin.castSucc Fin.castSucc := by
  rw [Matrix.mul_assoc, mul_inclCastSucc, projCastSucc_mul, Matrix.submatrix_submatrix]
  rfl

/-! ### The two square matrices built from the annihilating vectors -/

/-- The identity with its last row replaced by `w`. -/
private def rowFrame (w : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).updateRow (Fin.last n) w

/-- The identity with its last column replaced by `u`. -/
private def colFrame (u : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).updateCol (Fin.last n) u

private theorem rowFrame_castSucc (w : Fin (n + 1) → R) (a : Fin n) (b : Fin (n + 1)) :
    rowFrame w a.castSucc b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) a.castSucc b := by
  rw [rowFrame, Matrix.updateRow_ne (Fin.castSucc_lt_last a).ne]

private theorem colFrame_castSucc (u : Fin (n + 1) → R) (a : Fin (n + 1)) (b : Fin n) :
    colFrame u a b.castSucc = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) a b.castSucc := by
  rw [colFrame, Matrix.updateCol_ne (Fin.castSucc_lt_last b).ne]

private theorem submatrix_rowFrame (w : Fin (n + 1) → R) :
    (rowFrame w).submatrix Fin.castSucc Fin.castSucc = 1 := by
  ext a b
  rw [Matrix.submatrix_apply, rowFrame_castSucc]
  simp [Matrix.one_apply]

private theorem submatrix_colFrame (u : Fin (n + 1) → R) :
    (colFrame u).submatrix Fin.castSucc Fin.castSucc = 1 := by
  ext a b
  rw [Matrix.submatrix_apply, colFrame_castSucc]
  simp [Matrix.one_apply]

private theorem det_rowFrame (w : Fin (n + 1) → R) : (rowFrame w).det = w (Fin.last n) := by
  rw [det_eq_mul_det_submatrix_castSucc_of_col _ ?_, submatrix_rowFrame, Matrix.det_one, mul_one,
    rowFrame, Matrix.updateRow_self]
  intro i hi
  rw [rowFrame, Matrix.updateRow_ne hi, Matrix.one_apply_ne hi]

private theorem det_colFrame (u : Fin (n + 1) → R) : (colFrame u).det = u (Fin.last n) := by
  rw [det_eq_mul_det_submatrix_castSucc_of_row _ ?_, submatrix_colFrame, Matrix.det_one, mul_one,
    colFrame, Matrix.updateCol_self]
  intro j hj
  rw [colFrame, Matrix.updateCol_ne hj, Matrix.one_apply_ne' hj]

private theorem projCastSucc_mul_rowFrame (w : Fin (n + 1) → R) :
    projCastSucc n R * rowFrame w = projCastSucc n R := by
  rw [projCastSucc_mul]
  ext a b
  rw [Matrix.submatrix_apply, rowFrame_castSucc]
  rfl

private theorem colFrame_mul_inclCastSucc (u : Fin (n + 1) → R) :
    colFrame u * inclCastSucc n R = inclCastSucc n R := by
  rw [mul_inclCastSucc]
  ext a b
  rw [Matrix.submatrix_apply, colFrame_castSucc]
  rfl

private theorem rowFrame_mul (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {w : Fin (n + 1) → R}
    (hw : w ᵥ* A = 0) :
    rowFrame w * A = inclCastSucc n R * (projCastSucc n R * A) := by
  rw [projCastSucc_mul]
  ext i k
  rcases eq_or_ne i (Fin.last n) with rfl | hi
  · have h1 : (rowFrame w * A) (Fin.last n) k = (w ᵥ* A) k := by
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, rowFrame, Matrix.updateRow_self]
    have h2 : ∀ j : Fin n, inclCastSucc n R (Fin.last n) j = 0 := fun j => by
      rw [inclCastSucc_apply]
      simp [(Fin.castSucc_lt_last j).ne']
    rw [h1, hw, Pi.zero_apply, Matrix.mul_apply]
    simp [h2]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    have h2 : ∀ j : Fin n, inclCastSucc n R i.castSucc j = if i = j then 1 else 0 := fun j => by
      rw [inclCastSucc_apply]
      simp [Fin.castSucc_inj]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [rowFrame_castSucc, h2, Matrix.one_apply, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.submatrix_apply, id]

private theorem mul_colFrame (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {u : Fin (n + 1) → R}
    (hu : A *ᵥ u = 0) :
    A * colFrame u = A * inclCastSucc n R * projCastSucc n R := by
  rw [mul_inclCastSucc]
  ext i k
  rcases eq_or_ne k (Fin.last n) with rfl | hk
  · have h1 : (A * colFrame u) i (Fin.last n) = (A *ᵥ u) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colFrame, Matrix.updateCol_self]
    have h2 : ∀ j : Fin n, projCastSucc n R j (Fin.last n) = 0 := fun j => by
      rw [projCastSucc_apply]
      simp [(Fin.castSucc_lt_last j).ne]
    rw [h1, hu, Pi.zero_apply, Matrix.mul_apply]
    simp [h2]
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    have h2 : ∀ j : Fin n, projCastSucc n R j k.castSucc = if j = k then 1 else 0 := fun j => by
      rw [projCastSucc_apply]
      simp [Fin.castSucc_inj]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [colFrame_castSucc, h2, Matrix.one_apply, mul_ite, mul_zero, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.submatrix_apply, id]

/-! ### Conjugation invariance of the corner minor -/

private theorem det_projCastSucc_mul_mul (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {w : Fin (n + 1) → R} (hwN : w ᵥ* N = w) (hw : IsUnit (w (Fin.last n))) :
    (projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R)).det = N.det := by
  have hdet : IsUnit (rowFrame w).det := by rw [det_rowFrame]; exact hw
  have hmul : rowFrame w * (rowFrame w)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hlast : rowFrame w (Fin.last n) = w := Matrix.updateRow_self
  have hrow : (rowFrame w * N * (rowFrame w)⁻¹) (Fin.last n) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) := by
    have h1 : (rowFrame w * N) (Fin.last n) = rowFrame w (Fin.last n) := by
      rw [Matrix.mul_apply_eq_vecMul, hlast, hwN]
    rw [Matrix.mul_apply_eq_vecMul, h1, ← Matrix.mul_apply_eq_vecMul, hmul]
  have hsub : (rowFrame w * N * (rowFrame w)⁻¹).submatrix Fin.castSucc Fin.castSucc =
      projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R) := by
    rw [← projCastSucc_mul_mul_inclCastSucc]
    calc projCastSucc n R * (rowFrame w * N * (rowFrame w)⁻¹) * inclCastSucc n R
        = projCastSucc n R * rowFrame w * (N * ((rowFrame w)⁻¹ * inclCastSucc n R)) := by
          simp only [Matrix.mul_assoc]
      _ = projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R) := by
          rw [projCastSucc_mul_rowFrame, Matrix.mul_assoc]
  have hone : (rowFrame w).det * ((rowFrame w)⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have hexp : (rowFrame w * N * (rowFrame w)⁻¹).det =
      (projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R)).det := by
    rw [det_eq_mul_det_submatrix_castSucc_of_row _ fun j hj => by
      rw [congrFun hrow j, Matrix.one_apply_ne' hj], hsub, congrFun hrow (Fin.last n),
      Matrix.one_apply_eq, one_mul]
  rw [← hexp, Matrix.det_mul, Matrix.det_mul]
  linear_combination N.det * hone

private theorem det_mul_mul_inclCastSucc (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {u : Fin (n + 1) → R} (hMu : M *ᵥ u = u) (hu : IsUnit (u (Fin.last n))) :
    (projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R).det = M.det := by
  have hdet : IsUnit (colFrame u).det := by rw [det_colFrame]; exact hu
  have hmul : (colFrame u)⁻¹ * colFrame u = 1 := Matrix.nonsing_inv_mul _ hdet
  have hUe : colFrame u *ᵥ Pi.single (Fin.last n) 1 = u := by
    rw [Matrix.mulVec_single_one]
    funext i
    rw [Matrix.col_apply, colFrame, Matrix.updateCol_self]
  have hUinv : (colFrame u)⁻¹ *ᵥ u = Pi.single (Fin.last n) 1 := by
    have h : (colFrame u)⁻¹ *ᵥ (colFrame u *ᵥ Pi.single (Fin.last n) 1) =
        Pi.single (Fin.last n) 1 := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    rwa [hUe] at h
  have key : ∀ i, ((colFrame u)⁻¹ * M * colFrame u) i (Fin.last n) =
      (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) i := by
    have hkey : ((colFrame u)⁻¹ * M * colFrame u) *ᵥ Pi.single (Fin.last n) 1 =
        Pi.single (Fin.last n) 1 := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUe, hMu, hUinv]
    intro i
    have h := congrFun hkey i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h
  have hsub : ((colFrame u)⁻¹ * M * colFrame u).submatrix Fin.castSucc Fin.castSucc =
      projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R := by
    rw [← projCastSucc_mul_mul_inclCastSucc]
    calc projCastSucc n R * ((colFrame u)⁻¹ * M * colFrame u) * inclCastSucc n R
        = projCastSucc n R * (colFrame u)⁻¹ * M * (colFrame u * inclCastSucc n R) := by
          simp only [Matrix.mul_assoc]
      _ = projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R := by
          rw [colFrame_mul_inclCastSucc]
  have hone : ((colFrame u)⁻¹).det * (colFrame u).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have hexp : ((colFrame u)⁻¹ * M * colFrame u).det =
      (projCastSucc n R * (colFrame u)⁻¹ * M * inclCastSucc n R).det := by
    rw [det_eq_mul_det_submatrix_castSucc_of_col _ fun i hi => by
      rw [key i, Pi.single_eq_of_ne hi], hsub, key (Fin.last n), Pi.single_eq_same, one_mul]
  rw [← hexp, Matrix.det_mul, Matrix.det_mul]
  linear_combination M.det * hone

/-- **The corner minor is a conjugation invariant on doubly singular matrices.** If a square
matrix `A` is annihilated on the right by a column vector `u` and on the left by a row vector `w`,
both of which have a unit in their last coordinate, then conjugating `A` by any invertible matrix
that fixes `u` and `w` leaves the determinant of `A.submatrix Fin.castSucc Fin.castSucc`
unchanged. -/
theorem det_submatrix_castSucc_conj (A N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {u w : Fin (n + 1) → R} (hAu : A *ᵥ u = 0) (hwA : w ᵥ* A = 0) (hNu : N *ᵥ u = u)
    (hwN : w ᵥ* N = w) (hN : IsUnit N.det) (hu : IsUnit (u (Fin.last n)))
    (hw : IsUnit (w (Fin.last n))) :
    ((N * A * N⁻¹).submatrix Fin.castSucc Fin.castSucc).det =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have hNinv : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv _ hN
  have hNinv' : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul _ hN
  have hNinvu : N⁻¹ *ᵥ u = u := by
    conv_lhs => rw [← hNu]
    rw [Matrix.mulVec_mulVec, hNinv', Matrix.one_mulVec]
  have hrowdet : IsUnit (rowFrame w).det := by rw [det_rowFrame]; exact hw
  have hcoldet : IsUnit (colFrame u).det := by rw [det_colFrame]; exact hu
  have hGinv : (rowFrame w)⁻¹ * rowFrame w = 1 := Matrix.nonsing_inv_mul _ hrowdet
  have hUinv : colFrame u * (colFrame u)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hcoldet
  -- the canonical factorisation of `A` through the corner index type
  have hA1 : (rowFrame w)⁻¹ * inclCastSucc n R * (projCastSucc n R * A) = A := by
    calc (rowFrame w)⁻¹ * inclCastSucc n R * (projCastSucc n R * A)
        = (rowFrame w)⁻¹ * (inclCastSucc n R * (projCastSucc n R * A)) := by
          rw [Matrix.mul_assoc]
      _ = A := by rw [← rowFrame_mul A hwA, ← Matrix.mul_assoc, hGinv, Matrix.one_mul]
  have hA2 : A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹) = A := by
    calc A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹)
        = A * inclCastSucc n R * projCastSucc n R * (colFrame u)⁻¹ :=
          (Matrix.mul_assoc _ _ _).symm
      _ = A := by rw [← mul_colFrame A hAu, Matrix.mul_assoc, hUinv, Matrix.mul_one]
  have hPA : projCastSucc n R * A =
      A.submatrix Fin.castSucc Fin.castSucc * (projCastSucc n R * (colFrame u)⁻¹) := by
    calc projCastSucc n R * A
        = projCastSucc n R * (A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹)) := by
          rw [hA2]
      _ = projCastSucc n R * A * inclCastSucc n R * (projCastSucc n R * (colFrame u)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [projCastSucc_mul_mul_inclCastSucc]
  have main : (N * A * N⁻¹).submatrix Fin.castSucc Fin.castSucc =
      projCastSucc n R * N * ((rowFrame w)⁻¹ * inclCastSucc n R) *
        (A.submatrix Fin.castSucc Fin.castSucc) *
        (projCastSucc n R * (colFrame u)⁻¹ * N⁻¹ * inclCastSucc n R) := by
    rw [← projCastSucc_mul_mul_inclCastSucc]
    conv_lhs => rw [← hA1]
    rw [hPA]
    simp only [Matrix.mul_assoc]
  rw [main, Matrix.det_mul, Matrix.det_mul,
    det_projCastSucc_mul_mul N hwN hw, det_mul_mul_inclCastSucc N⁻¹ hNinvu hu]
  have hone : N.det * (N⁻¹).det = 1 := by rw [← Matrix.det_mul, hNinv, Matrix.det_one]
  linear_combination (A.submatrix Fin.castSucc Fin.castSucc).det * hone

end Matrix
