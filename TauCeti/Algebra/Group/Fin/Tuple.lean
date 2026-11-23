/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Appending to a tuple and the zero tuple

A tuple `Fin.snoc v x` is zero exactly when `v` and `x` are both zero. This is the `Fin.snoc`
counterpart of Mathlib's `Matrix.cons_eq_zero_iff` and `Matrix.cons_ne_zero_iff`.

## Main results

* `Fin.snoc_eq_zero_iff`: `Fin.snoc v x = 0` if and only if `v = 0` and `x = 0`.
* `Fin.snoc_ne_zero_iff`: `Fin.snoc v x ≠ 0` if and only if `v ≠ 0` or `x ≠ 0`.
-/

public section

namespace Fin

variable {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, Zero (α i)]

/-- Appending `x` to `v` gives the zero tuple if and only if `v` and `x` are both zero. -/
@[simp]
theorem snoc_eq_zero_iff {v : ∀ i : Fin n, α i.castSucc} {x : α (last n)} :
    snoc v x = 0 ↔ v = 0 ∧ x = 0 := by
  rw [← snoc_init_self (0 : ∀ i, α i), snoc_inj]
  simp [init_def, Pi.zero_def]

/-- Appending `x` to `v` gives a nonzero tuple if and only if `v` or `x` is nonzero. -/
theorem snoc_ne_zero_iff {v : ∀ i : Fin n, α i.castSucc} {x : α (last n)} :
    snoc v x ≠ 0 ↔ v ≠ 0 ∨ x ≠ 0 := by
  rw [Ne, snoc_eq_zero_iff, not_and_or]

end Fin
