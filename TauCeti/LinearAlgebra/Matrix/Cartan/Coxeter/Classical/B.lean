/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.A
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Coxeter element of type `Bₙ` has order `2n`

In the `ε`-model of type `Bₙ` (Mathlib's numbering, short simple root last) the simple roots are
`αᵢ = εᵢ - εᵢ₊₁` for `i < n - 1` and `α_{n-1} = ε_{n-1}` (`TauCeti.Coxeter.epsB`, a unimodular
matrix). The simple reflections become the transpositions `(i i+1)` and the sign change of the last
coordinate, and the Coxeter element becomes the negacyclic shift `εᵢ ↦ εᵢ₊₁`, `ε_{n-1} ↦ -ε₀`, whose
`n`-th power is `-1`. Hence the order is `2n`.
-/

public section

open Matrix Equiv.Perm

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- The `ε`-coordinates of the simple roots of type `Bₙ`: column `i` is `εᵢ - εᵢ₊₁`, and the
last column is `ε_{n-1}`. -/
@[expose] def epsB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a i => (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0)

/-- The sign change of the last coordinate. -/
@[expose] def flipLast (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun a => if a.val + 1 = n then -1 else 1

/-- A long simple reflection of type `Bₙ` is a transposition in the `ε`-model. -/
theorem epsB_mul_reflMatrix_of_lt (i : Fin n) (hi : i.val + 1 < n) :
    epsB n * reflMatrix (CartanMatrix.B n) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, hi⟩) * epsB n := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  simp only [epsB, CartanMatrix.B, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> (try simp only at *) <;> omega

/-- The short simple reflection of type `Bₙ` is the sign change of the last coordinate. -/
theorem epsB_mul_reflMatrix_last (i : Fin n) (hi : i.val + 1 = n) :
    epsB n * reflMatrix (CartanMatrix.B n) i = flipLast n * epsB n := by
  ext a j
  rw [mul_reflMatrix_apply, flipLast, diagonal_mul]
  simp only [epsB, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The negacyclic shift `εᵢ ↦ εᵢ₊₁`, `ε_{n-1} ↦ -ε₀`. -/
@[expose] def negaShift (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => if b.val + 1 = a.val then 1 else if b.val + 1 = n ∧ a.val = 0 then -1 else 0

/-- **The Coxeter element of type `Bₙ` is the negacyclic shift** in the `ε`-model. -/
theorem epsB_mul_coxeterElement {m : ℕ} :
    epsB (m + 1) * coxeterElement (CartanMatrix.B (m + 1)) = negaShift (m + 1) * epsB (m + 1) := by
  have hlist : ∀ l : List (Fin m), epsB (m + 1) *
      (l.map (reflMatrix (CartanMatrix.B (m + 1)) ∘ Fin.castSucc)).prod =
      permMatrixHom (R := ℤ) (l.map adjSwap).prod * epsB (m + 1) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, Function.comp_apply,
        epsB_mul_reflMatrix_of_lt i.castSucc (by simp), Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
        List.map_cons, List.prod_cons, map_mul]
      rfl
  rw [coxeterElement, List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
    ← Matrix.mul_assoc, hlist, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Matrix.mul_one, Matrix.mul_assoc, epsB_mul_reflMatrix_last _ (by simp), ← Matrix.mul_assoc,
    prod_adjSwap_eq_finRotate]
  congr 1
  ext a b
  rw [permMatrixHom_mul_apply]
  simp only [flipLast, diagonal_apply, negaShift, Matrix.of_apply]
  have hσ : (finRotate (m + 1)).symm a = b ↔ a.val = if b.val = m then 0 else b.val + 1 := by
    rw [Equiv.symm_apply_eq, Fin.ext_iff, coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
  by_cases hb : b.val + 1 < m + 1
  · rw [ite_eq_right (by omega)] at hσ
    by_cases hab : (finRotate (m + 1)).symm a = b
    · have := hσ.1 hab
      rw [ite_eq_left hab, hab, ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right hab, ite_eq_right (fun h => hab (hσ.2 (by omega))),
        ite_eq_right (by omega)]
  · have hb' : b.val + 1 = m + 1 := by omega
    rw [ite_eq_left (by omega)] at hσ
    by_cases hab : (finRotate (m + 1)).symm a = b
    · have := hσ.1 hab
      rw [ite_eq_left hab, hab, ite_eq_left hb', ite_eq_right (by omega),
        ite_eq_left ⟨hb', this⟩]
    · rw [ite_eq_right hab, ite_eq_right (by omega), ite_eq_right (fun h => hab (hσ.2 h.2))]

/-- Closed form of the powers `negaShift n ^ k` for `k ≤ n`. -/
theorem negaShift_pow {m : ℕ} {k : ℕ} (hk : k ≤ m + 1) (a b : Fin (m + 1)) :
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
        simp only [negaShift, Matrix.of_apply, Fin.val_last, true_and]
        split_ifs <;> omega
      · intro c _ hc
        have hc' : c.val ≠ m := fun h => hc (Fin.ext h)
        simp only [negaShift, Matrix.of_apply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
      · simp
    · rw [Finset.sum_eq_single ⟨a.val - 1, by omega⟩]
      · rw [ih (by omega)]
        simp only [negaShift, Matrix.of_apply]
        split_ifs <;> omega
      · intro c _ hc
        have hc' : c.val ≠ a.val - 1 := fun h => hc (Fin.ext h)
        simp only [negaShift, Matrix.of_apply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
      · simp

theorem negaShift_pow_self {m : ℕ} : negaShift (m + 1) ^ (m + 1) = -1 := by
  ext a b
  rw [negaShift_pow le_rfl]
  simp only [Matrix.neg_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The negacyclic shift on `ℤⁿ` has order `2n`.** -/
theorem orderOf_negaShift {m : ℕ} : orderOf (negaShift (m + 1)) = 2 * (m + 1) := by
  rw [orderOf_eq_iff (by omega)]
  refine ⟨by rw [mul_comm, pow_mul, negaShift_pow_self]; simp, fun k hk hk0 h => ?_⟩
  by_cases hkn : k ≤ m + 1
  · by_cases hkn' : k = m + 1
    · subst hkn'
      have := congrFun (congrFun h 0) 0
      rw [negaShift_pow_self] at this
      simp at this
    · have := congrFun (congrFun h ⟨k, by omega⟩) 0
      rw [negaShift_pow hkn] at this
      simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
      split_ifs at this <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = (m + 1) + j := ⟨k - (m + 1), by omega⟩
    have := congrFun (congrFun h ⟨j, by omega⟩) 0
    rw [pow_add, negaShift_pow_self, neg_one_mul, Matrix.neg_apply, negaShift_pow (by omega)]
      at this
    simp only [Fin.val_zero, Matrix.one_apply, Fin.ext_iff] at this
    split_ifs at this <;> omega

/-- Partial sums: the inverse of `epsB`. -/
@[expose] def epsBInv (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i a => if a.val ≤ i.val then 1 else 0

theorem epsBInv_mul_epsB : epsBInv n * epsB n = 1 := by
  ext i k
  simp only [epsBInv, epsB, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_sub,
    mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k (fun a _ ha =>
      ite_eq_right_iff.2 fun h => absurd (Fin.ext h) ha) (by simp)]
  by_cases hk : k.val + 1 < n
  · rw [Finset.sum_eq_single ⟨k.val + 1, hk⟩ (fun a _ ha =>
        ite_eq_right_iff.2 fun h => absurd (Fin.ext h) ha) (by simp)]
    simp only [Fin.ext_iff, ite_true]
    split_ifs <;> omega
  · rw [Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.2 fun h => absurd h (by omega))]
    simp only [Fin.ext_iff, ite_true]
    split_ifs <;> omega

theorem epsB_mul_epsBInv : epsB n * epsBInv n = 1 :=
  mul_eq_one_comm.1 epsBInv_mul_epsB

/-- **The Coxeter element of type `Bₙ` has order `2n`.** -/
theorem orderOf_coxeterElement_B (m : ℕ) :
    orderOf (coxeterElement (CartanMatrix.B (m + 1))) = 2 * (m + 1) := by
  rw [← orderOf_negaShift]
  refine orderOf_eq_orderOf_of_mul_eq_mul epsB_mul_coxeterElement (fun k h => ?_) fun k h => ?_
  · rw [← Matrix.one_mul (coxeterElement (CartanMatrix.B (m + 1)) ^ k), ← epsBInv_mul_epsB,
      Matrix.mul_assoc, h]
  · rw [← Matrix.mul_one (negaShift (m + 1) ^ k), ← epsB_mul_epsBInv, ← Matrix.mul_assoc, h]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.B, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ <;> first | exact absurd h₁ hij | omega

end TauCeti.Coxeter

end
