/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# `p`-series: a clean constant bound beyond exponent two, and shifted weights on `ℤ`

`∑' m : ℕ, m ^ (-t) ≤ 2` for every real `t ≥ 2`. Mathlib supplies the exact value at the endpoint,
`ζ (2) = π ^ 2 / 6`, and summability throughout `t > 1`, but no inequality valid across a range of
exponents; that is what this file adds.

The bound is deliberately lossy. The supremum over `t ≥ 2` is `ζ (2) = 1.6449…`, so `2` gives away
about 18%. A round constant is the useful thing to expose: consumers carry it through chains of
inequalities and none of them wants `π` in the goal.

Nothing here is specific to any application, and the file contains no number theory. The `m = 0`
term is `0`, by the junk value of `0 ^ (-t)`.

The file also records the summability over `ℤ` of the shifted weights `(1 + |n|) ^ r` for
`r < -1`, the form in which the `p`-series enters weighted sequence spaces.

## Main results

* `TauCeti.tsum_nat_rpow_neg_le_two` — `∑' m : ℕ, m ^ (-t) ≤ 2` for `2 ≤ t`.
* `TauCeti.summable_one_add_abs_int_rpow` — `∑ n : ℤ, (1 + |n|) ^ r` converges for `r < -1`.
-/

public section

namespace TauCeti

/-- **The `p`-series over `ℕ` is at most `2` beyond exponent two.** For `2 ≤ t`,
`∑' m : ℕ, m ^ (-t) ≤ 2`, the case `t = 2` being `ζ(2) = π ^ 2 / 6 < 2`.  The `m = 0` term is
`0`, by the junk value of `0 ^ (-t)`. -/
theorem tsum_nat_rpow_neg_le_two {t : ℝ} (ht : 2 ≤ t) : ∑' m : ℕ, (m : ℝ) ^ (-t) ≤ 2 := by
  have hsum : ∀ u : ℝ, 1 < u → Summable fun m : ℕ ↦ (m : ℝ) ^ (-u) := fun u hu ↦
    Real.summable_nat_rpow.mpr (by linarith)
  have hfun : (fun m : ℕ ↦ (m : ℝ) ^ (-(2 : ℝ))) = fun m : ℕ ↦ (1 : ℝ) / (m : ℝ) ^ 2 := by
    funext m
    rw [Real.rpow_neg (Nat.cast_nonneg m), Real.rpow_two, one_div]
  have hzeta : ∑' m : ℕ, (m : ℝ) ^ (-(2 : ℝ)) = Real.pi ^ 2 / 6 := by
    rw [hfun]
    exact hasSum_zeta_two.tsum_eq
  refine le_trans (Summable.tsum_le_tsum (fun m ↦ ?_) (hsum t (by linarith))
    (hsum 2 one_lt_two)) ?_
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by norm_num)]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  · rw [hzeta]
    nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- The weights `(1 + |n|) ^ r` are summable over `ℤ` for `r < -1`. -/
theorem summable_one_add_abs_int_rpow {r : ℝ} (hr : r < -1) :
    Summable fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ r := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := -r) (by linarith))
    ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [neg_neg, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.2 (Int.cast_ne_zero.2 hn))
    (le_add_of_nonneg_left zero_le_one) (by linarith)

end TauCeti

