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
`D = diag (2, …, 2, 1)` symmetrizes `Cₙ` on the left (`D * Cₙ` is symmetric), equivalently `Bₙ` on
the right, and it intertwines the simple reflections of the two types over `ℤ`:
`D sᵢ^B = sᵢ^C D` (`TauCeti.Coxeter.dB_mul_reflMatrix_B`). Since `D` is cancellable, the two Coxeter
elements have the same order (`Matrix.orderOf_eq_orderOf_of_isLeftRegular`), which is `2n` for
`n ≥ 1`.
-/

public section

open Matrix

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- The diagonal matrix `diag (2, …, 2, 1)`. It symmetrizes the `Cₙ` Cartan matrix on the left
(`dB n * CartanMatrix.C n` is symmetric), equivalently the `Bₙ` Cartan matrix on the right. -/
def dB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun a => if a.val + 1 = n then 1 else 2

theorem dB_apply (a b : Fin n) : dB n a b = if a = b then (if a.val + 1 = n then 1 else 2) else 0 :=
  diagonal_apply _ _ _

/-- **`diag (2, …, 2, 1)` intertwines the simple reflections of types `Bₙ` and `Cₙ`.** -/
theorem dB_mul_reflMatrix_B (i : Fin n) :
    dB n * reflMatrix (CartanMatrix.B n) i = reflMatrix (CartanMatrix.C n) i * dB n := by
  ext k j
  rw [dB, diagonal_mul, mul_diagonal]
  simp only [reflMatrix, CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **`diag (2, …, 2, 1)` intertwines the Coxeter elements of types `Bₙ` and `Cₙ`.** -/
theorem dB_mul_coxeterElement :
    dB n * coxeterElement (CartanMatrix.B n) = coxeterElement (CartanMatrix.C n) * dB n :=
  mul_prod_map_eq_prod_map_mul dB_mul_reflMatrix_B _

/-- `dB` can be cancelled on the left: its diagonal entries are nonzero. -/
theorem isLeftRegular_dB : IsLeftRegular (dB n) := fun X Y h => by
  ext a j
  have := congrFun (congrFun h a) j
  simp only [dB, diagonal_mul] at this
  exact mul_left_cancel₀ (by split_ifs <;> norm_num) this

/-- **The Coxeter element of type `Cₙ` has order `2n`** for `n ≥ 1`. -/
theorem orderOf_coxeterElement_C (hn : 1 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.C n)) = 2 * n := by
  rw [← orderOf_coxeterElement_B hn,
    orderOf_eq_orderOf_of_isLeftRegular dB_mul_coxeterElement isLeftRegular_dB]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.C, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ <;> first | exact absurd h₁ hij | omega

end TauCeti.Coxeter

end
