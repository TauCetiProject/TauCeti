/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.Convex.FourPoint
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
`Real.norm_one_div_add_pow_add_one_div_add_sub_pow_le` bounds the paired shifted summands
by the sum at the endpoints using `TauCeti.add_le_add_of_convexOn_of_add_eq`.

## Main results

* `TauCeti.summable_one_add_abs_int_rpow` — `∑ n : ℤ, (1 + |n|) ^ r` converges for `r < -1`.
-/

public section

open Filter Set

namespace Real

/-- Moving two positive bases towards one another with their sum fixed bounds the
norm of the sum of their reciprocal powers by the original reciprocal-power sum. -/
theorem norm_one_div_add_pow_add_one_div_add_sub_pow_le {a s t : ℝ}
    (ha : 0 < a) (ht : t ∈ Icc 0 s) (k : ℕ) :
    ‖1 / (a + t) ^ k + 1 / (a + s - t) ^ k‖ ≤ 1 / a ^ k + 1 / (a + s) ^ k := by
  have hf : ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ 1 / x ^ k) := by
    simpa only [zpow_neg, zpow_natCast, one_div] using (convexOn_zpow (𝕜 := ℝ) (-(k : ℤ)))
  have ht₀ : 0 ≤ t := ht.1
  have hb : 0 < a + s := by linarith [ht.2]
  have hb' : 0 < a + s - t := by linarith [ht.2]
  rw [norm_of_nonneg (by positivity)]
  exact TauCeti.add_le_add_of_convexOn_of_add_eq hf ha hb (by linarith)
    (by linarith [ht.2]) (by ring)

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

/-- The weights `(1 + |n|) ^ r` are summable over `ℤ` for `r < -1`. -/
theorem summable_one_add_abs_int_rpow {r : ℝ} (hr : r < -1) :
    Summable fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ r := by
  have h := Real.summable_abs_int_rpow (b := -r) (by linarith)
  rw [neg_neg] at h
  exact h.const_add_rpow (by linarith) ((Filter.eventually_cofinite_ne 0).mono fun n hn ↦
    abs_pos.2 (Int.cast_ne_zero.2 hn)) 1

end TauCeti
