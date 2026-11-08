/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.LinearCombination

/-!
# Plane rotations with nonzero entries

A point `(c, s)` of the unit circle in a commutative ring gives the plane rotation
`!![c, -s; s, c]`, an orthogonal matrix. Extended by the identity it is an orthogonal `n × n`
matrix for every `n ≥ 2` whose first row has the entries `c` and `-s`. So as soon as `c * s ≠ 0`
there is an orthogonal matrix `A` and labels `a ≠ b` with `A a a * A a b ≠ 0`: an orthogonal
matrix that is not a signed permutation matrix.

## Main results

* `TauCeti.exists_orthogonal_apply_mul_apply_ne_zero`: such an orthogonal matrix exists.
-/

public section

open Matrix

namespace TauCeti

/-- In dimension at least two, a plane rotation through `c` and `s` is an orthogonal matrix with
`A a a * A a b ≠ 0` for two distinct labels `a` and `b`, as soon as `c * s ≠ 0`. -/
theorem exists_orthogonal_apply_mul_apply_ne_zero {R : Type*} [CommRing R] {n : ℕ} (hn : 2 ≤ n)
    (hrot : ∃ c s : R, c ^ 2 + s ^ 2 = 1 ∧ c * s ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) R, Aᵀ * A = 1 ∧ ∃ a b, a ≠ b ∧ A a a * A a b ≠ 0 := by
  obtain ⟨c, s, hcs, hcs0⟩ := hrot
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  set e : Fin 2 ⊕ Fin m ≃ Fin (2 + m) := finSumFinEquiv
  set B : Matrix (Fin 2) (Fin 2) R := !![c, -s; s, c]
  have hB : Bᵀ * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [B, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, transpose_apply,
        of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, Fin.sum_univ_two,
        mul_neg, neg_mul, neg_neg, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, one_apply_eq,
        one_apply_ne] <;>
      first | linear_combination hcs | ring1
  refine ⟨reindex e e (fromBlocks B 0 0 1), ?_, e (.inl 0), e (.inl 1), by simp, ?_⟩
  · rw [transpose_reindex, ← coe_reindexAlgEquiv R R, ← map_mul, fromBlocks_transpose,
      fromBlocks_multiply]
    simp [hB]
  · simpa [B] using hcs0

end TauCeti
