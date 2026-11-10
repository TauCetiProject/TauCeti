/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.B

/-!
# The Coxeter element of type `Cₙ` has order `2n`

Mathlib's `Cₙ` Cartan matrix is the transpose of the `Bₙ` one. The diagonal matrix
`D = diag (2, …, 2, 1)` symmetrizes `Bₙ`, and it intertwines the simple reflections of the two types
over `ℤ`: `D sᵢ^B = sᵢ^C D` (`TauCeti.Coxeter.dB_mul_reflMatrix_B`). Since `D` is cancellable, the
two Coxeter elements have the same order, `2n`.
-/

public section

open Matrix

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- The symmetrizer `diag (2, …, 2, 1)` of the `Bₙ` Cartan matrix. -/
@[expose] def dB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => if a = b then (if a.val + 1 = n then 1 else 2) else 0

theorem dB_mul_apply {k : Type*} (M : Matrix (Fin n) k ℤ) (a : Fin n) (j : k) :
    (dB n * M) a j = (if a.val + 1 = n then 1 else 2) * M a j := by
  simp only [dB, Matrix.mul_apply, Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem mul_dB_apply {k : Type*} (M : Matrix k (Fin n) ℤ) (a : k) (j : Fin n) :
    (M * dB n) a j = M a j * (if j.val + 1 = n then 1 else 2) := by
  simp only [dB, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem dB_mul_reflMatrix_B (i : Fin n) :
    dB n * reflMatrix (CartanMatrix.B n) i = reflMatrix (CartanMatrix.C n) i * dB n := by
  ext k j
  rw [dB_mul_apply, mul_dB_apply]
  simp only [reflMatrix, CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem dB_mul_coxeterElement :
    dB n * coxeterElement (CartanMatrix.B n) = coxeterElement (CartanMatrix.C n) * dB n := by
  have : ∀ l : List (Fin n), dB n * (l.map (reflMatrix (CartanMatrix.B n))).prod =
      (l.map (reflMatrix (CartanMatrix.C n))).prod * dB n := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, dB_mul_reflMatrix_B,
        Matrix.mul_assoc, ih, ← Matrix.mul_assoc, List.map_cons, List.prod_cons]
  exact this _

theorem dB_mul_left_cancel {X Y : Matrix (Fin n) (Fin n) ℤ} (h : dB n * X = dB n * Y) :
    X = Y := by
  ext a j
  have := congrFun (congrFun h a) j
  rw [dB_mul_apply, dB_mul_apply] at this
  exact mul_left_cancel₀ (by split_ifs <;> norm_num) this

theorem dB_mul_right_cancel {X Y : Matrix (Fin n) (Fin n) ℤ} (h : X * dB n = Y * dB n) :
    X = Y := by
  ext a j
  have := congrFun (congrFun h a) j
  rw [mul_dB_apply, mul_dB_apply] at this
  exact mul_right_cancel₀ (by split_ifs <;> norm_num) this

/-- **The Coxeter element of type `Cₙ` has order `2n`.** -/
theorem orderOf_coxeterElement_C (m : ℕ) :
    orderOf (coxeterElement (CartanMatrix.C (m + 1))) = 2 * (m + 1) := by
  rw [← orderOf_coxeterElement_B m]
  have hpow : ∀ k, dB (m + 1) * coxeterElement (CartanMatrix.B (m + 1)) ^ k =
      coxeterElement (CartanMatrix.C (m + 1)) ^ k * dB (m + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, dB_mul_coxeterElement,
        ← Matrix.mul_assoc, ← pow_succ]
  refine orderOf_eq_orderOf_iff.2 fun k => ⟨fun h => dB_mul_left_cancel ?_,
    fun h => dB_mul_right_cancel ?_⟩
  · rw [hpow, h, Matrix.one_mul, Matrix.mul_one]
  · rw [← hpow, h, Matrix.one_mul, Matrix.mul_one]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.C, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ <;> first | exact absurd h₁ hij | omega

end TauCeti.Coxeter

end
