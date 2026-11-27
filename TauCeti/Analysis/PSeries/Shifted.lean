/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# Shifted `p`-series

The weights `(1 + |n|) ^ r` are summable over `n : ℤ` for `r < -1`. This is the form in which the
`p`-series enters weighted sequence spaces. It follows from Mathlib's `Real.summable_abs_int_rpow`
(the unshifted series `∑ |n| ^ (-b)` for `1 < b`) by the general comparison
`Summable.const_add_rpow`: shifting a base that is positive outside a finite set by a constant
keeps a summable family of nonpositive powers summable.

For real translates of the naturals, `Real.summable_one_div_nat_add_pow_iff` gives the exact
convergence criterion for reciprocal natural powers.
`TauCeti.hasSum_one_div_sub_pow_add_one_div_add_pow` uses this criterion to split the paired
series into the nearest term and the remaining paired tail.

## Main results

* `TauCeti.summable_one_add_abs_int_rpow` — `∑ n : ℤ, (1 + |n|) ^ r` converges for `r < -1`.
-/

public section

open Filter Set

namespace Real

/-- The reciprocal natural-power series of any real translate of the naturals
is summable exactly when its exponent exceeds one. -/
theorem summable_one_div_nat_add_pow_iff (a : ℝ) {k : ℕ} :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + a) ^ k) ↔ 1 < k := by
  have heq : (fun n : ℕ ↦ 1 / ((n : ℝ) + a) ^ k) =ᶠ[atTop]
      (fun n : ℕ ↦ 1 / |(n : ℝ) + a| ^ (k : ℝ)) := by
    filter_upwards [eventually_gt_atTop ⌈|a|⌉₊] with n hn
    have hna : |a| < (n : ℝ) := Nat.lt_of_ceil_lt hn
    rw [abs_of_pos (by linarith [neg_abs_le a]), rpow_natCast]
  rw [summable_congr_atTop heq, summable_one_div_nat_add_rpow]
  norm_cast

end Real

namespace TauCeti

/-- The paired reciprocal-power series converges for every shift when `k > 1`. Its sum
splits into the term at `1 - |t|` and the paired tail with successive starting indices. -/
theorem hasSum_one_div_sub_pow_add_one_div_add_pow {k : ℕ} (hk : 1 < k) (t : ℝ) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 - t) ^ k + 1 / ((n : ℝ) + 1 + t) ^ k)
      (1 / (1 - |t|) ^ k +
        ∑' n : ℕ, (1 / ((n : ℝ) + 1 + |t|) ^ k + 1 / ((n : ℝ) + 2 - |t|) ^ k)) := by
  have heven (n : ℕ) :
      1 / ((n : ℝ) + 1 - t) ^ k + 1 / ((n : ℝ) + 1 + t) ^ k =
        1 / ((n : ℝ) + 1 - |t|) ^ k + 1 / ((n : ℝ) + 1 + |t|) ^ k := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · simp only [abs_of_neg h, sub_eq_add_neg, neg_neg]
      exact add_comm _ _
  have hminus : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 - |t|) ^ k) := by
    simpa only [add_sub_assoc] using (Real.summable_one_div_nat_add_pow_iff (1 - |t|)).mpr hk
  have hplus : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 + |t|) ^ k) := by
    simpa only [add_assoc] using (Real.summable_one_div_nat_add_pow_iff (1 + |t|)).mpr hk
  convert ((hminus.add hplus).hasSum.congr_fun fun n ↦ heven n) using 1
  symm
  rw [hminus.tsum_add hplus, hminus.tsum_eq_zero_add, add_assoc]
  simp only [Nat.cast_zero, zero_add]
  congr 1
  have hshift : Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1 - |t|) ^ k) :=
    hminus.comp_injective Nat.succ_injective
  rw [← hshift.tsum_add hplus]
  refine tsum_congr fun n ↦ ?_
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
  exact add_comm _ _

/-- The weights `(1 + |n|) ^ r` are summable over `ℤ` for `r < -1`. -/
theorem summable_one_add_abs_int_rpow {r : ℝ} (hr : r < -1) :
    Summable fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ r := by
  have h := Real.summable_abs_int_rpow (b := -r) (by linarith)
  rw [neg_neg] at h
  exact h.const_add_rpow (by linarith) ((Filter.eventually_cofinite_ne 0).mono fun n hn ↦
    abs_pos.2 (Int.cast_ne_zero.2 hn)) 1

end TauCeti
