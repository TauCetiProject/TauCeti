/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic

/-!
# Iterates of the shift

A complement to Mathlib's `SymbolicDynamics.FullShift.mulShift`: iterating the shift by `g`
`k` times is the shift by `g ^ k` (in additive notation, by `k • g`).

## Main results

* `SymbolicDynamics.FullShift.mulShift_iterate`, `SymbolicDynamics.FullShift.shift_iterate`:
  `(mulShift g)^[k] = mulShift (g ^ k)` and `(shift g)^[k] = shift (k • g)`.
-/

public section

namespace SymbolicDynamics.FullShift

variable {A G : Type*} [Monoid G]

/-- Iterating the shift by `g` `k` times is the shift by `g ^ k`. -/
@[to_additive (attr := simp) /-- Iterating the shift by `g` `k` times is the shift by `k • g`. -/]
theorem mulShift_iterate (g : G) (k : ℕ) : (mulShift (A := A) g)^[k] = mulShift (g ^ k) := by
  induction k with
  | zero => funext x; simp
  | succ k ih => rw [Function.iterate_succ', ih, pow_succ]; funext x; simp [mulShift_mul]

end SymbolicDynamics.FullShift
