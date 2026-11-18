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
two Coxeter elements have the same order, `2n` (`Matrix.orderOf_eq_orderOf_of_mul_eq_mul`).
-/

public section

open Matrix

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- The symmetrizer `diag (2, …, 2, 1)` of the `Bₙ` Cartan matrix. -/
@[expose] def dB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun a => if a.val + 1 = n then 1 else 2

theorem dB_mul_reflMatrix_B (i : Fin n) :
    dB n * reflMatrix (CartanMatrix.B n) i = reflMatrix (CartanMatrix.C n) i * dB n := by
  ext k j
  rw [dB, diagonal_mul, mul_diagonal]
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
  simp only [dB, diagonal_mul] at this
  exact mul_left_cancel₀ (by split_ifs <;> norm_num) this

theorem dB_mul_right_cancel {X Y : Matrix (Fin n) (Fin n) ℤ} (h : X * dB n = Y * dB n) :
    X = Y := by
  ext a j
  have := congrFun (congrFun h a) j
  simp only [dB, mul_diagonal] at this
  exact mul_right_cancel₀ (by split_ifs <;> norm_num) this

/-- **The Coxeter element of type `Cₙ` has order `2n`.** -/
theorem orderOf_coxeterElement_C (m : ℕ) :
    orderOf (coxeterElement (CartanMatrix.C (m + 1))) = 2 * (m + 1) := by
  rw [← orderOf_coxeterElement_B m, orderOf_eq_orderOf_of_mul_eq_mul dB_mul_coxeterElement
    (fun k h => dB_mul_left_cancel (h.trans (Matrix.mul_one _).symm))
    (fun k h => dB_mul_right_cancel (h.trans (Matrix.one_mul _).symm))]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.C, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ <;> first | exact absurd h₁ hij | omega

end TauCeti.Coxeter

end
