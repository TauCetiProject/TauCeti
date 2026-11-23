/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.A
public import TauCeti.LinearAlgebra.Matrix.NegaShift
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Coxeter element of type `Bₙ` has order `2n`

In the `ε`-model of type `Bₙ` (Mathlib's numbering, short simple root last) the simple roots are
`αᵢ = εᵢ - εᵢ₊₁` for `i < n - 1` and `α_{n-1} = ε_{n-1}` (`TauCeti.Coxeter.epsB`, the type-`Aₙ`
matrix `TauCeti.Coxeter.epsA` without its last row; it is unimodular, with inverse the partial-sum
matrix `TauCeti.Coxeter.epsBInv`). The simple reflections become the transpositions `(i i+1)` and
the sign change of the last coordinate, and the Coxeter element becomes the negacyclic shift
`Matrix.negaShift ℤ n`: `εᵢ ↦ εᵢ₊₁`, `ε_{n-1} ↦ -ε₀`, whose `n`-th power is `-1`. Hence for `n ≥ 1`
the order is `2n`.
-/

public section

open Matrix Equiv.Perm

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- The `ε`-coordinates of the simple roots of type `Bₙ`: column `i` is `εᵢ - εᵢ₊₁`, and the
last column is `ε_{n-1}`. This is `epsA n` with its last row (the coordinate `εₙ`) dropped. -/
def epsB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (epsA n).submatrix Fin.castSucc id

theorem epsB_apply (a i : Fin n) :
    epsB n a i = (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0) := by
  simp only [epsB, submatrix_apply, id_eq, epsA_apply, Fin.val_castSucc]

/-- The sign change of the last coordinate. -/
private def flipLast (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun a => if a.val + 1 = n then -1 else 1

/-- A long simple reflection of type `Bₙ` is a transposition in the `ε`-model. -/
theorem epsB_mul_reflMatrix_of_lt (i : Fin n) (hi : i.val + 1 < n) :
    epsB n * reflMatrix (CartanMatrix.B n) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, hi⟩) * epsB n := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  simp only [epsB_apply, CartanMatrix.B, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> (try simp only at *) <;> omega

/-- The short simple reflection of type `Bₙ` is the sign change of the last coordinate. -/
private theorem epsB_mul_reflMatrix_last (i : Fin n) (hi : i.val + 1 = n) :
    epsB n * reflMatrix (CartanMatrix.B n) i = flipLast n * epsB n := by
  ext a j
  rw [mul_reflMatrix_apply, flipLast, diagonal_mul]
  simp only [epsB_apply, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The short simple reflection of type `Bₙ` changes the sign of the last coordinate** in the
`ε`-model. -/
theorem epsB_mul_reflMatrix_last_apply (i : Fin n) (hi : i.val + 1 = n) (a j : Fin n) :
    (epsB n * reflMatrix (CartanMatrix.B n) i) a j =
      if a.val + 1 = n then -epsB n a j else epsB n a j := by
  rw [epsB_mul_reflMatrix_last i hi, flipLast, diagonal_mul]
  split_ifs <;> simp

/-- **The Coxeter element of type `Bₙ` is the negacyclic shift** in the `ε`-model. -/
theorem epsB_mul_coxeterElement :
    epsB n * coxeterElement (CartanMatrix.B n) = negaShift ℤ n * epsB n := by
  rcases n with _ | m
  · exact Subsingleton.elim _ _
  rw [coxeterElement, mul_prod_map_finRange_succ_eq_permMatrixHom_finRotate_mul_mul
    epsB_mul_reflMatrix_of_lt (epsB_mul_reflMatrix_last _ (by simp))]
  congr 1
  ext a b
  rw [permMatrixHom_mul_apply]
  obtain ⟨x, rfl⟩ := (finRotate (m + 1)).surjective a
  rw [Equiv.symm_apply_apply]
  simp only [flipLast, diagonal_apply, negaShift_apply, coe_finRotate, Fin.ext_iff, Fin.val_last]
  have := x.isLt
  have := b.isLt
  split_ifs <;> first | omega | simp_all

/-- Partial sums: the inverse of `epsB`. This is `epsALeftInv n` with its last column dropped. -/
def epsBInv (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (epsALeftInv n).submatrix id Fin.castSucc

theorem epsBInv_apply (i a : Fin n) : epsBInv n i a = if a.val ≤ i.val then 1 else 0 := by
  simp only [epsBInv, submatrix_apply, id_eq, epsALeftInv_apply, Fin.val_castSucc]

/-- `epsBInv` is a left inverse of `epsB`: the column of `epsALeftInv n` dropped in `epsBInv` is
zero, so this is `epsALeftInv_mul_epsA`. -/
@[simp]
theorem epsBInv_mul_epsB : epsBInv n * epsB n = 1 := by
  rw [← epsALeftInv_mul_epsA]
  ext i k
  simp only [epsBInv, epsB, Matrix.mul_apply, submatrix_apply, id_eq]
  rw [Fin.sum_univ_castSucc, epsALeftInv_apply, Fin.val_last,
    ite_eq_right (by have := i.isLt; omega), zero_mul, add_zero]

/-- `epsBInv` is also a right inverse of `epsB`. -/
@[simp]
theorem epsB_mul_epsBInv : epsB n * epsBInv n = 1 :=
  mul_eq_one_comm.mp epsBInv_mul_epsB

/-- `epsB` can be cancelled on the left: it has the left inverse `epsBInv`. -/
theorem isLeftRegular_epsB : IsLeftRegular (epsB n) :=
  mul_right_injective_of_inv _ _ epsBInv_mul_epsB

/-- **The Coxeter element of type `Bₙ` has order `2n`** for `n ≥ 1`. -/
theorem orderOf_coxeterElement_B (hn : 1 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.B n)) = 2 * n := by
  rw [orderOf_eq_orderOf_of_isLeftRegular epsB_mul_coxeterElement isLeftRegular_epsB,
    orderOf_negaShift hn (by decide)]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.B, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ <;> first | exact absurd h₁ hij | omega

end TauCeti.Coxeter

end
