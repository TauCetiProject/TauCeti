/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.A
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# The Coxeter element of type `Bₙ` has order `2n`

In the `ε`-model of type `Bₙ` (Mathlib's numbering, short simple root last) the simple roots are
`αᵢ = εᵢ - εᵢ₊₁` for `i < n - 1` and `α_{n-1} = ε_{n-1}` (`TauCeti.Coxeter.epsB`, the type-`Aₙ`
matrix `TauCeti.Coxeter.epsA` without its last row; it is unimodular, with inverse the partial-sum
matrix `TauCeti.Coxeter.epsBInv`). The simple reflections become the transpositions `(i i+1)` and
the sign change of the last coordinate, and the Coxeter element becomes the negacyclic shift
`εᵢ ↦ εᵢ₊₁`, `ε_{n-1} ↦ -ε₀`, whose `n`-th power is `-1`. Hence the order is `2n`.
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

/-- The negacyclic shift `εᵢ ↦ εᵢ₊₁`, `ε_{n-1} ↦ -ε₀`. -/
def negaShift (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => if b.val + 1 = a.val then 1 else if b.val + 1 = n ∧ a.val = 0 then -1 else 0

theorem negaShift_apply (a b : Fin n) :
    negaShift n a b =
      if b.val + 1 = a.val then 1 else if b.val + 1 = n ∧ a.val = 0 then -1 else 0 :=
  (rfl)

/-- **The Coxeter element of type `Bₙ` is the negacyclic shift** in the `ε`-model. -/
theorem epsB_mul_coxeterElement {m : ℕ} :
    epsB (m + 1) * coxeterElement (CartanMatrix.B (m + 1)) = negaShift (m + 1) * epsB (m + 1) := by
  have hlong : ∀ i : Fin m, epsB (m + 1) * reflMatrix (CartanMatrix.B (m + 1)) i.castSucc =
      permMatrixHom (R := ℤ) (BraidGroup.transposition (n := m + 1) i) * epsB (m + 1) :=
    fun i => by
      rw [BraidGroup.transposition_eq_swap_castSucc_succ,
        show i.succ = ⟨i.castSucc.val + 1, by simp⟩ from Fin.ext (by simp)]
      exact epsB_mul_reflMatrix_of_lt _ _
  rw [coxeterElement, List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    Function.comp_def, ← Matrix.mul_assoc,
    mul_prod_map_finRange_eq_permMatrixHom_finRotate_mul hlong, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_assoc,
    epsB_mul_reflMatrix_last _ (by simp), ← Matrix.mul_assoc]
  congr 1
  ext a b
  rw [permMatrixHom_mul_apply]
  obtain ⟨x, rfl⟩ := (finRotate (m + 1)).surjective a
  rw [Equiv.symm_apply_apply]
  simp only [flipLast, diagonal_apply, negaShift_apply, coe_finRotate, Fin.ext_iff, Fin.val_last]
  have := x.isLt
  have := b.isLt
  split_ifs <;> first | omega | simp_all

/-- Closed form of the powers `negaShift n ^ k` for `k ≤ n`. -/
theorem negaShift_pow_apply {m : ℕ} {k : ℕ} (hk : k ≤ m + 1) (a b : Fin (m + 1)) :
    (negaShift (m + 1) ^ k) a b =
      if a.val = b.val + k then 1 else if a.val + (m + 1) = b.val + k then -1 else 0 := by
  induction k generalizing a with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Fin.ext_iff, add_zero]
    split_ifs <;> omega
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    by_cases ha : a.val = 0
    · rw [Finset.sum_eq_single (Fin.last m)]
      · rw [ih (by omega)]
        simp only [negaShift_apply, Fin.val_last, true_and]
        split_ifs <;> omega
      · intro c _ hc
        have hc' : c.val ≠ m := fun h => hc (Fin.ext h)
        simp only [negaShift_apply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
      · simp
    · rw [Finset.sum_eq_single ⟨a.val - 1, by omega⟩]
      · rw [ih (by omega)]
        simp only [negaShift_apply]
        split_ifs <;> omega
      · intro c _ hc
        have hc' : c.val ≠ a.val - 1 := fun h => hc (Fin.ext h)
        simp only [negaShift_apply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
      · simp

/-- The `n`-th power of the negacyclic shift on `ℤⁿ` is `-1`. -/
theorem negaShift_pow_eq_neg_one {m : ℕ} : negaShift (m + 1) ^ (m + 1) = -1 := by
  ext a b
  rw [negaShift_pow_apply le_rfl]
  simp only [Matrix.neg_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The negacyclic shift on `ℤⁿ` has order `2n`.** -/
theorem orderOf_negaShift {m : ℕ} : orderOf (negaShift (m + 1)) = 2 * (m + 1) := by
  rw [orderOf_eq_iff (by omega)]
  refine ⟨by rw [mul_comm, pow_mul, negaShift_pow_eq_neg_one]; simp, fun k hk hk0 h => ?_⟩
  by_cases hkn : k ≤ m + 1
  · by_cases hkn' : k = m + 1
    · subst hkn'
      have := congrFun (congrFun h 0) 0
      rw [negaShift_pow_eq_neg_one] at this
      simp at this
    · have := congrFun (congrFun h ⟨k, by omega⟩) 0
      rw [negaShift_pow_apply hkn] at this
      simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
      split_ifs at this <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = (m + 1) + j := ⟨k - (m + 1), by omega⟩
    have := congrFun (congrFun h ⟨j, by omega⟩) 0
    rw [pow_add, negaShift_pow_eq_neg_one, neg_one_mul, Matrix.neg_apply,
      negaShift_pow_apply (by omega)] at this
    simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
    split_ifs at this <;> omega

/-- Partial sums: the inverse of `epsB`. This is `epsALeftInv n` with its last column dropped. -/
def epsBInv (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (epsALeftInv n).submatrix id Fin.castSucc

theorem epsBInv_apply (i a : Fin n) : epsBInv n i a = if a.val ≤ i.val then 1 else 0 := by
  simp only [epsBInv, submatrix_apply, id_eq, epsALeftInv_apply, Fin.val_castSucc]

/-- `epsBInv` is a left inverse of `epsB`: the column of `epsALeftInv n` dropped in `epsBInv` is
zero, so this is `epsALeftInv_mul_epsA`. -/
theorem epsBInv_mul_epsB : epsBInv n * epsB n = 1 := by
  rw [← epsALeftInv_mul_epsA]
  ext i k
  simp only [epsBInv, epsB, Matrix.mul_apply, submatrix_apply, id_eq]
  rw [Fin.sum_univ_castSucc, epsALeftInv_apply, Fin.val_last,
    ite_eq_right (by have := i.isLt; omega), zero_mul, add_zero]

/-- `epsB` can be cancelled on the left (it has the left inverse `epsBInv`), hence also on the
right (`Matrix.isLeftRegular_iff_isRightRegular`). -/
theorem isLeftRegular_epsB : IsLeftRegular (epsB n) :=
  mul_right_injective_of_inv _ _ epsBInv_mul_epsB

/-- **The Coxeter element of type `Bₙ` has order `2n`.** -/
theorem orderOf_coxeterElement_B (hn : 1 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.B n)) = 2 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← orderOf_negaShift, orderOf_eq_orderOf_of_mul_eq_mul epsB_mul_coxeterElement
    (fun k h => isLeftRegular_epsB (h.trans (Matrix.mul_one _).symm))
    (fun k h => isLeftRegular_iff_isRightRegular.mp isLeftRegular_epsB
      (h.trans (Matrix.one_mul _).symm))]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.B, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ <;> first | exact absurd h₁ hij | omega

end TauCeti.Coxeter

end
