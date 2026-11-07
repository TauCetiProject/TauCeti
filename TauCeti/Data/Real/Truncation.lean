/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Truncating real numbers to `[-r, r]`

Truncating two reals to `[-r, r]` does not increase the positive part of their sum
(`ENNReal.ofReal_max_neg_min_add_max_neg_min_le`), and a fixed real number is eventually unchanged
by truncation to `[-n, n]` as `n → ∞` (`Real.eventually_max_neg_min_eq`).
-/

public section

/-- Truncating two reals to `[-r, r]` does not increase the positive part of their sum. -/
theorem ENNReal.ofReal_max_neg_min_add_max_neg_min_le {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    ENNReal.ofReal (max (-r) (min a r) + max (-r) (min b r)) ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_le_ofReal_iff']
  rcases le_total 0 (a + b) with h | h
  · left
    simp only [max_def, min_def]
    split_ifs <;> linarith
  · right
    simp only [max_def, min_def]
    split_ifs <;> linarith

/-- A real number is eventually unchanged by truncation to `[-n, n]`. -/
theorem Real.eventually_max_neg_min_eq (a : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, max (-(n : ℝ)) (min a n) = a := by
  obtain ⟨N, hN⟩ := exists_nat_ge |a|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hle : |a| ≤ n := hN.trans (Nat.cast_le.2 hn)
  simp only [min_eq_left (abs_le.1 hle).2, max_eq_right (abs_le.1 hle).1]
