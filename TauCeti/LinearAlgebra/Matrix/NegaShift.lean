/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.GroupTheory.OrderOfElement
import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion

/-!
# The negacyclic shift

The negacyclic shift `Matrix.negaShift n` on `ℤⁿ` sends `eᵢ ↦ eᵢ₊₁` for `i + 1 < n` and
`e_{n-1} ↦ -e₀`. Its `n`-th power is `-1` (`Matrix.negaShift_pow_eq_neg_one`), so for `n ≥ 1` it
has order `2n` (`Matrix.orderOf_negaShift`). Up to relabelling it is the companion matrix of
`Xⁿ + 1`, which is therefore its characteristic polynomial (`Matrix.charpoly_negaShift`).

It is the Coxeter element of type `Bₙ` in the `ε`-model.
-/

public section

open Polynomial

namespace Matrix

/-- The negacyclic shift `eᵢ ↦ eᵢ₊₁`, `e_{n-1} ↦ -e₀`. -/
def negaShift (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => if b.val + 1 = a.val then 1 else if b.val + 1 = n ∧ a.val = 0 then -1 else 0

theorem negaShift_apply {n : ℕ} (a b : Fin n) :
    negaShift n a b =
      if b.val + 1 = a.val then 1 else if b.val + 1 = n ∧ a.val = 0 then -1 else 0 :=
  (rfl)

/-- Closed form of the powers `negaShift n ^ k` for `k ≤ n`. -/
theorem negaShift_pow_apply {n k : ℕ} (hk : k ≤ n) (a b : Fin n) :
    (negaShift n ^ k) a b =
      if a.val = b.val + k then 1 else if a.val + n = b.val + k then -1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := b.isLt; omega⟩
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
theorem negaShift_pow_eq_neg_one (n : ℕ) : negaShift n ^ n = -1 := by
  ext a b
  rw [negaShift_pow_apply le_rfl]
  simp only [Matrix.neg_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The negacyclic shift on `ℤⁿ` has order `2n`** for `n ≥ 1`. -/
theorem orderOf_negaShift {n : ℕ} (hn : 1 ≤ n) : orderOf (negaShift n) = 2 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
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

/-- **The negacyclic shift on `ℤⁿ` has characteristic polynomial `Xⁿ + 1`** for `n ≥ 1`: up to
relabelling, it is the companion matrix of `Xⁿ + 1`. -/
theorem charpoly_negaShift {n : ℕ} (hn : 1 ≤ n) : (negaShift n).charpoly = X ^ n + 1 := by
  have hdeg : (X ^ n + 1 : ℤ[X]).natDegree = n := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by simp; omega), natDegree_X_pow]
  have hmon : (X ^ n + 1 : ℤ[X]).Monic := by
    simpa using monic_X_pow_add_C (1 : ℤ) (n := n) (by omega)
  have h : negaShift n = reindex (finCongr hdeg) (finCongr hdeg) (X ^ n + 1 : ℤ[X]).companion := by
    ext a b
    simp only [reindex_apply, submatrix_apply, finCongr_symm, finCongr_apply, companion_apply,
      Fin.val_cast, negaShift_apply, hdeg, coeff_add, coeff_X_pow, coeff_one]
    split_ifs <;> omega
  rw [h, charpoly_reindex, charpoly_companion hmon]

end Matrix

end
