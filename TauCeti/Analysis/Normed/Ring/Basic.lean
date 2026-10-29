/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Elementary inequalities in seminormed rings

This file records elementary consequences of the submultiplicativity of the norm.
-/

public section

namespace TauCeti

/-- A product of two elements in the open unit ball again belongs to the open unit ball. -/
theorem norm_mul_lt_one {K : Type*} [NonUnitalSeminormedRing K] (u v : K) (hu : ‖u‖ < 1)
    (hv : ‖v‖ < 1) : ‖u * v‖ < 1 := by
  calc
    ‖u * v‖ ≤ ‖u‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ ‖u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.le (norm_nonneg u)
    _ < 1 := hu

/-- Consecutive powers stay in the open unit ball when the first factor is strictly inside
and the second factor is in the closed unit ball. -/
theorem norm_pow_succ_mul_pow_lt_one {K : Type*} [SeminormedRing K]
    (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖u ^ (n + 1) * v ^ n‖ < 1 := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa using hu
  calc
    ‖u ^ (n + 1) * v ^ n‖ ≤ ‖u ^ (n + 1)‖ * ‖v ^ n‖ := norm_mul_le _ _
    _ ≤ ‖u‖ ^ (n + 1) * ‖v‖ ^ n :=
      mul_le_mul (norm_pow_le' _ (Nat.succ_pos n)) (norm_pow_le' _ hn) (norm_nonneg _)
        (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖u‖ ^ (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv)
        (pow_nonneg (norm_nonneg _) _)
    _ < 1 := by simpa using pow_lt_one₀ (norm_nonneg _) hu (Nat.succ_ne_zero n)

/-- For `‖q‖ < 1` also `‖qⁿ‖ < 1` for every `n ≠ 0`. -/
theorem norm_pow_lt_one {R : Type*} [SeminormedRing R] {q : R} (hq : ‖q‖ < 1) {n : ℕ}
    (hn : n ≠ 0) : ‖q ^ n‖ < 1 :=
  (norm_pow_le' q (Nat.pos_of_ne_zero hn)).trans_lt (pow_lt_one₀ (norm_nonneg q) hq hn)

end TauCeti

end
