/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Differences of powers in a seminormed ring

The telescoping identity `aⁿ⁺¹ - bⁿ⁺¹ = a (aⁿ - bⁿ) + (a - b) bⁿ` bounds a difference of powers by
the difference of the bases: `‖aⁿ - bⁿ‖ ≤ ‖a - b‖ n max(‖a‖, ‖b‖)ⁿ⁻¹`. This is the normed
counterpart of `abs_pow_sub_pow_le` for linearly ordered rings; it needs neither commutativity
nor `‖1‖ ≤ 1`. It compares `zⁿ` with `(z')ⁿ` when `z` and `z'` are close relative to their size,
for instance a point of a vertical strip with its imaginary part.
-/

public section

/-- A difference of `n`-th powers is at most `n` times the difference of the bases times the
`(n - 1)`-st power of the larger norm. -/
theorem norm_pow_sub_pow_le {R : Type*} [SeminormedRing R] (a b : R) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ * n * max ‖a‖ ‖b‖ ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    set M := max ‖a‖ ‖b‖
    have hb : ‖b ^ n‖ ≤ M ^ n :=
      (norm_pow_le' b hn).trans (pow_le_pow_left₀ (norm_nonneg b) (le_max_right _ _) n)
    have hMn : M ^ (n - 1) * ‖a‖ ≤ M ^ n := by
      rw [← pow_sub_one_mul (by omega : n ≠ 0)]
      gcongr
      exact le_max_left _ _
    calc
      ‖a ^ (n + 1) - b ^ (n + 1)‖ = ‖a * (a ^ n - b ^ n) + (a - b) * b ^ n‖ := by
        rw [pow_succ', pow_succ' b, mul_sub, sub_mul, sub_add_sub_cancel]
      _ ≤ ‖a‖ * ‖a ^ n - b ^ n‖ + ‖a - b‖ * ‖b ^ n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖a‖ * (‖a - b‖ * n * M ^ (n - 1)) + ‖a - b‖ * M ^ n := by gcongr
      _ = ‖a - b‖ * n * (M ^ (n - 1) * ‖a‖) + ‖a - b‖ * M ^ n := by ring
      _ ≤ ‖a - b‖ * n * M ^ n + ‖a - b‖ * M ^ n := by gcongr
      _ = ‖a - b‖ * ↑(n + 1) * M ^ (n + 1 - 1) := by
        rw [add_tsub_cancel_right]
        push_cast
        ring
