/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.Analysis.Asymptotics.NatFloor

/-!
# One-sided prime remainder bounds at real cutoffs

The signed prime remainder changes by at most `26 / y` between `⌊y⌋₊` and a nonnegative
cutoff `y`. This lets the integer-cutoff estimate imply the upper bound at real cutoffs
with any positive exponent loss. The floor argument and choice of exponents are those of
`New.eventually_primeRemainder_le_rpow` in `grh/src/New/Reduction/OneSidedBound.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Filter
open scoped Nat

namespace TauCeti.OneSidedBound

/-- Rounding a nonnegative cutoff down to a natural number changes the signed prime remainder
by at most `26 / y`. -/
theorem abs_primeRemainder_sub_nat_floor_le (d q : ℕ) [Fact d.Prime] [NeZero q]
    {y : ℝ} (hy : 0 ≤ y) :
    |primeRemainder d q y - primeRemainder d q ⌊y⌋₊| ≤ 26 / y := by
  rcases le_or_gt 1 y with h₁ | h₁
  · have hfloor : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
      exact_mod_cast (Nat.one_le_floor_iff y).2 h₁
    have hgap := Nat.lt_floor_add_one y
    calc
      _ ≤ 13 * (y - ⌊y⌋₊) / ⌊y⌋₊ :=
        abs_primeRemainder_sub_le d q (zero_lt_one.trans_le hfloor) (Nat.floor_le hy)
      _ ≤ 13 / ⌊y⌋₊ := by gcongr; linarith
      _ ≤ 13 / (y / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 26 / y := by ring
  · have hfloor := Nat.floor_eq_zero.mpr h₁
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    have hdiff : primeRemainder d q y - primeRemainder d q ⌊y⌋₊ = -Real.log y / q.totient := by
      simp only [primeRemainder_def, hfloor, Nat.cast_zero, Nat.floor_zero, Real.log_zero,
        Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, zero_div, sub_zero]
      ring
    have hlog : Real.log y ≤ 0 := Real.log_nonpos hy h₁.le
    rw [hdiff, abs_of_nonneg (div_nonneg (neg_nonneg.mpr hlog) (by positivity))]
    calc
      _ ≤ -Real.log y := div_le_self (neg_nonneg.mpr hlog) hφ
      _ ≤ y⁻¹ := by linarith only [Real.neg_inv_le_log hy]
      _ ≤ 26 / y := by rw [← one_div]; gcongr; norm_num

/-- The integer-cutoff bound with exponent `-1/2 + 6 * δ` for every sufficiently small `δ > 0`
implies the one-sided bound with exponent `-1/2 + ε` at real cutoffs for every `ε > 0`. -/
theorem eventually_primeRemainder_le_rpow (d q : ℕ) [Fact d.Prime] [NeZero q] {C ε : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∀ᶠ n : ℕ in atTop, primeRemainder d q n ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ) + 6 * δ))
    (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (-(1 / 2 : ℝ) + ε) := by
  let δ : ℝ := min (1 / 200) (ε / 7)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ < 1 / 100 := (min_le_left ..).trans_lt (by norm_num)
  have hδε : 6 * δ < ε := by linarith [min_le_right (1 / 200) (ε / 7)]
  refine eventually_le_rpow_of_nat_floor (D := 26) (by linarith) (by linarith) (h δ hδ hδ₁) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  exact (le_abs_self _).trans (abs_primeRemainder_sub_nat_floor_le d q hy)

end TauCeti.OneSidedBound
