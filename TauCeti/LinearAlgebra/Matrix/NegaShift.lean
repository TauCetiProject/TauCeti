/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.GroupTheory.OrderOfElement
import TauCeti.Algebra.Polynomial.Monic
import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion

/-!
# The negacyclic shift

The negacyclic shift `Matrix.negaShift R n` on `Rⁿ` sends `eᵢ ↦ eᵢ₊₁` for `i + 1 < n` and
`e_{n-1} ↦ -e₀`. Over any ring its `n`-th power is `-1` (`Matrix.negaShift_pow_eq_neg_one`), so
for `n ≥ 1` it has order `2n` as soon as `-1 ≠ 1` (`Matrix.orderOf_negaShift`). Its entries are
those of the companion matrix of `Xⁿ + 1`, which is therefore its characteristic polynomial
(`Matrix.charpoly_negaShift`).

Over `ℤ` the negacyclic shift is the Coxeter element of type `Bₙ` in the `ε`-model.
-/

public section

open Polynomial

namespace Matrix

section Ring

variable {R : Type*} [Ring R]

variable (R) in
/-- The negacyclic shift `eᵢ ↦ eᵢ₊₁`, `e_{n-1} ↦ -e₀`. -/
def negaShift (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => if b.val + 1 = a.val then 1 else if b.val + 1 = n ∧ a.val = 0 then -1 else 0

theorem negaShift_apply {n : ℕ} (a b : Fin n) :
    negaShift R n a b =
      if b.val + 1 = a.val then 1 else if b.val + 1 = n ∧ a.val = 0 then -1 else 0 :=
  (rfl)

/-- Closed form of the powers `negaShift R n ^ k` for `k ≤ n`. -/
theorem negaShift_pow_apply {n k : ℕ} (hk : k ≤ n) (a b : Fin n) :
    (negaShift R n ^ k) a b =
      if a.val = b.val + k then 1 else if a.val + n = b.val + k then -1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := b.isLt; omega⟩
  induction k generalizing a with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Fin.ext_iff, add_zero]
    split_ifs <;> first | omega | rfl
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    by_cases ha : a.val = 0
    · rw [Finset.sum_eq_single (Fin.last m)]
      · rw [ih (by omega)]
        simp only [negaShift_apply, Fin.val_last, true_and]
        split_ifs <;> first | omega | simp
      · intro c _ hc
        have hc' : c.val ≠ m := fun h => hc (Fin.ext h)
        simp only [negaShift_apply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
      · simp
    · rw [Finset.sum_eq_single ⟨a.val - 1, by omega⟩]
      · rw [ih (by omega)]
        simp only [negaShift_apply]
        split_ifs <;> first | omega | simp
      · intro c _ hc
        have hc' : c.val ≠ a.val - 1 := fun h => hc (Fin.ext h)
        simp only [negaShift_apply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
      · simp

/-- The `n`-th power of the negacyclic shift on `Rⁿ` is `-1`. -/
@[simp]
theorem negaShift_pow_eq_neg_one (n : ℕ) : negaShift R n ^ n = -1 := by
  ext a b
  rw [negaShift_pow_apply le_rfl]
  simp only [Matrix.neg_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | omega | simp

/-- **The negacyclic shift on `Rⁿ` has order `2n`** for `n ≥ 1`, provided `-1 ≠ 1` in `R` (for
instance when `ringChar R ≠ 2`, `Ring.neg_one_ne_one_of_char_ne_two`). -/
theorem orderOf_negaShift {n : ℕ} (hn : 1 ≤ n) (hR : (-1 : R) ≠ 1) :
    orderOf (negaShift R n) = 2 * n := by
  have : Nontrivial R := ⟨⟨-1, 1, hR⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [orderOf_eq_iff (by omega)]
  refine ⟨by rw [mul_comm, pow_mul, negaShift_pow_eq_neg_one]; simp, fun k hk hk0 h => ?_⟩
  by_cases hkn : k ≤ m + 1
  · by_cases hkn' : k = m + 1
    · subst hkn'
      have := congrFun (congrFun h 0) 0
      rw [negaShift_pow_eq_neg_one, Matrix.neg_apply, Matrix.one_apply_eq] at this
      exact hR this
    · have := congrFun (congrFun h ⟨k, by omega⟩) 0
      rw [negaShift_pow_apply hkn] at this
      simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
      have hk0' : k ≠ 0 := by omega
      rw [ite_eq_right hk0'] at this
      split_ifs at this <;> first | omega | exact absurd this (by simp)
  · obtain ⟨j, rfl⟩ : ∃ j, k = (m + 1) + j := ⟨k - (m + 1), by omega⟩
    have := congrFun (congrFun h ⟨j, by omega⟩) 0
    rw [pow_add, negaShift_pow_eq_neg_one, neg_one_mul, Matrix.neg_apply,
      negaShift_pow_apply (by omega)] at this
    simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
    have hj : j ≠ 0 := by omega
    rw [ite_eq_right hj] at this
    split_ifs at this <;> first | omega | exact absurd this (by simp)

end Ring

/-- **The negacyclic shift on `Rⁿ` has characteristic polynomial `Xⁿ + 1`** for `n ≥ 1`: it has
the entries of the companion matrix of `Xⁿ + 1`. -/
theorem charpoly_negaShift {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) :
    (negaShift R n).charpoly = X ^ n + 1 := by
  refine charpoly_eq_of_apply_eq_companion (monic_X_pow_add_one (by omega))
    (by rw [← C_1, natDegree_X_pow_add_C]) fun a b => ?_
  simp only [negaShift_apply, coeff_add, coeff_X_pow, coeff_one]
  split_ifs <;> first | omega | simp

end Matrix

end
