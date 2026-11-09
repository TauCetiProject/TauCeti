/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Bounded sequences satisfying a doubling Cauchy–Schwarz inequality

A real sequence `b` with `0 ≤ b 0` that is bounded above and satisfies the inequality
`b n ^ 2 ≤ b 0 * b (n + n)` cannot increase at the first step: `b 1 ≤ b 0`. If it did, the ratio
`r = b 1 / b 0` would exceed `1` and repeated doubling would push `b (2 ^ k)` past
`b 0 * r ^ (2 ^ k)`, which is unbounded.

The inequality is the shape of the Cauchy–Schwarz inequality for a positive-semidefinite Hankel
sequence, or for the correlations `ω (a⋆ α_{is}(a))` of a positive functional invariant under a
one-parameter group `α`.

## Main declarations

* `TauCeti.apply_one_le_apply_zero_of_sq_le_mul`: such a sequence satisfies `b 1 ≤ b 0`.
-/

public section

namespace TauCeti

/-- A bounded sequence of reals with `0 ≤ b 0` whose squares satisfy the Cauchy–Schwarz
inequality `b n ^ 2 ≤ b 0 * b (n + n)` cannot increase at the first step. -/
theorem apply_one_le_apply_zero_of_sq_le_mul {b : ℕ → ℝ} {D : ℝ} (hb0 : 0 ≤ b 0)
    (hsq : ∀ n, b n ^ 2 ≤ b 0 * b (n + n)) (hbd : ∀ n, b n ≤ D) : b 1 ≤ b 0 := by
  rcases le_or_gt (b 1) (b 0) with hle | hlt
  · exact hle
  exfalso
  have hb0pos : 0 < b 0 := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · have h1 := hsq 1
      rw [← h] at h1
      nlinarith
  set r : ℝ := b 1 / b 0 with hr
  have hr1 : 1 < r := (one_lt_div hb0pos).mpr hlt
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have key : ∀ k : ℕ, b 0 * r ^ 2 ^ k ≤ b (2 ^ k) := by
    intro k
    induction k with
    | zero =>
        have : b 0 * r = b 1 := by
          rw [hr, mul_div_cancel₀ _ hb0pos.ne']
        simpa using this.le
    | succ k ih =>
        have hpow : (0 : ℝ) < r ^ 2 ^ k := pow_pos hrpos _
        have hsplit : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        have hsq' := hsq (2 ^ k)
        have hrw : r ^ 2 ^ (k + 1) = (r ^ 2 ^ k) ^ 2 := by
          rw [hsplit, pow_add, sq]
        rw [hrw, hsplit]
        nlinarith [mul_pos hb0pos hpow]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (D / b 0) hr1
  have hD : D < b 0 * r ^ k := by
    rw [mul_comm]
    exact (div_lt_iff₀ hb0pos).mp hk
  have hmono : r ^ k ≤ r ^ 2 ^ k :=
    pow_le_pow_right₀ hr1.le (Nat.le_of_lt k.lt_two_pow_self)
  have hchain : b 0 * r ^ k ≤ D :=
    le_trans (le_trans (mul_le_mul_of_nonneg_left hmono hb0pos.le) (key k)) (hbd _)
  linarith

end TauCeti
