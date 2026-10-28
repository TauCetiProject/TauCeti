/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# Positive odd terms in an arithmetic progression

A progression with positive step contains a positive odd term if either its initial
term or its step is odd. The index can be chosen nonnegative. This is useful when a translation
must fix a congruence class while also arranging the sign and parity of a matrix entry.
-/

public section

namespace Int

/-- A progression with positive step contains a positive odd term at a nonnegative index if its
initial term or its step is odd. -/
theorem exists_nat_add_mul_pos_odd (a : ℤ) {c : ℤ} (hc : 0 < c)
    (hodd : Odd a ∨ Odd c) : ∃ j : ℕ, 0 < a + j * c ∧ Odd (a + j * c) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  have hpos : 0 < a + (2 * (n + 1) : ℕ) * c := by
    push_cast
    have : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    nlinarith
  by_cases ha : Odd a
  · refine ⟨2 * (n + 1), hpos, ?_⟩
    have hj : Even (((2 * (n + 1) : ℕ) : ℤ)) := by exact_mod_cast even_two_mul (n + 1)
    exact ha.add_even (hj.mul_right c)
  · have hcodd := hodd.resolve_left ha
    refine ⟨2 * (n + 1) + 1, ?_, ?_⟩
    · push_cast at hpos ⊢
      nlinarith
    · have hj : Odd (((2 * (n + 1) + 1 : ℕ) : ℤ)) := by
        exact_mod_cast odd_two_mul_add_one (n + 1)
      exact (Int.not_odd_iff_even.mp ha).add_odd (hj.mul hcodd)

end Int
