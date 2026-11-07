/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Monotone.Basic

/-!
# Sequences with multiplicative growth

A sequence `h` in a linearly ordered semiring with `L ≤ h 0` for some `L > 0`, and
`M h k ≤ h (k + 1)` for some `M ≥ 1`, is positive and monotone
(`forall_pos_and_monotone_of_mul_le`). This is how a sequence of heights growing by a fixed factor
is seen to be positive and monotone.
-/

public section

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A sequence `h` with `L ≤ h 0` and `M h k ≤ h (k + 1)` for `M ≥ 1` and `L > 0` is positive and
monotone. -/
theorem forall_pos_and_monotone_of_mul_le {h : ℕ → R} {M L : R} (hM : 1 ≤ M) (hL : 0 < L)
    (h₀ : L ≤ h 0) (hh : ∀ k, M * h k ≤ h (k + 1)) : (∀ k, 0 < h k) ∧ Monotone h := by
  have hpos : ∀ k, 0 < h k := by
    intro k
    induction k with
    | zero => exact hL.trans_le h₀
    | succ k ih => exact (mul_pos (zero_lt_one.trans_le hM) ih).trans_le (hh k)
  exact ⟨hpos, monotone_nat_of_le_succ fun k ↦ (le_mul_of_one_le_left (hpos k).le hM).trans (hh k)⟩
