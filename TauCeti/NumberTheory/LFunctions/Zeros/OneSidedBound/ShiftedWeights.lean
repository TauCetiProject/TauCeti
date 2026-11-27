/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.WeightBounds

/-!
# Logarithmic stability of two-cutoff weights

A shift in a derivative order has a small logarithmic cost when both base weights come
from separated cutoffs. The estimate applies to the integral quotient `x * b / x₁`
as well as to the high weight `b`, without needing exact divisibility.

The order and logarithmic estimate follow `New.Data.log_shiftedWeight_le` in
`grh/src/New/Reduction/Data/LevelAndTwists.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

namespace TauCeti.OneSidedBound

/-- At the two cutoff weights, a shift of index at most `4m` increases the logarithm by at most
`1 / x`. The scale condition `x ^ 42 * x₁ ≤ b` does not require exact division at the small
weight. -/
theorem log_shifted_cutoff_weight_le {x x₁ b m r i : ℕ} (large : Prop) [Decidable large]
    (hx : 3 ^ 8 ≤ x) (hxx₁ : x ≤ x₁) (hb : x ^ 42 * x₁ ≤ b)
    (hm : m ^ 2 ≤ 4 * x) (hr : r ≤ 3 * x ^ 5) (hi : i ≤ 4 * m) :
    let κ := if large then b else x * b / x₁
    Real.log ((κ + (i + 1) * r ^ 8 : ℕ) : ℝ) ≤ Real.log κ + 1 / (x : ℝ) := by
  intro κ
  have hsmall : x ^ 43 ≤ x * b / x₁ := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < x₁)).2
    rw [pow_succ', mul_assoc]
    exact Nat.mul_le_mul_left _ hb
  have hbase : x ^ 43 ≤ κ := by
    by_cases h : large
    · simpa only [κ, ite_eq_left h] using hsmall.trans
        (Nat.div_le_of_le_mul (Nat.mul_le_mul_right b hxx₁))
    · simpa only [κ, ite_eq_right h] using hsmall
  have hshift := (shiftedWeight_mem_Icc (κ := 0) hx hm hr hi).2
  exact log_shiftedWeight_le hbase (by simpa only [Nat.zero_add] using hshift)

end TauCeti.OneSidedBound
