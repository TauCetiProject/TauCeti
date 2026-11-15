/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# Sequences with vanishing second differences

A sequence `f : ℕ → G` in an additive commutative group with
`f i + f (i + 2) = 2 • f (i + 1)` for all indices `i` with `i + 2 < N` is affine on the indices
below `N`: it equals `f 0 + i • (f 1 - f 0)` there. The bound `N` makes the statement usable
for finite sequences, such as data indexed along a chain of fixed length.

## Main results

* `TauCeti.eq_add_nsmul_sub_of_add_eq_two_nsmul`: a sequence whose second differences vanish
  below `N` is affine below `N`.
-/

public section

namespace TauCeti

variable {G : Type*} [AddCommGroup G]

/-- A sequence with `f i + f (i + 2) = 2 • f (i + 1)` below `N` is affine below `N`. -/
theorem eq_add_nsmul_sub_of_add_eq_two_nsmul {f : ℕ → G} {N : ℕ}
    (hf : ∀ i, i + 2 < N → f i + f (i + 2) = 2 • f (i + 1)) :
    ∀ i < N, f i = f 0 + i • (f 1 - f 0) := by
  intro i
  induction i using Nat.twoStepInduction with
  | zero => intro; simp
  | one => intro; rw [one_nsmul, add_sub_cancel]
  | more i hi hi₁ =>
      intro hin
      have h := hf i (by omega)
      rw [hi (by omega), hi₁ (by omega)] at h
      rw [eq_sub_of_add_eq' h, add_nsmul, add_nsmul, succ_nsmul]
      abel

end TauCeti
