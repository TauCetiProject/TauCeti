/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.WeakPNT
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.LogIntegral

/-!
# Prime counts in fixed multiplicative intervals

For a fixed `c ≥ 1`, the number of primes in `(x, c * x]`, normalized by `x / log x`, tends to
`c - 1`. The equal-endpoint case `c = 1` is included. The proof uses the qualitative prime number
theorem at both endpoints and the fact that adding a constant to `log x` preserves its asymptotic.

In particular, the number of primes in `(x, 3 * x]` eventually lies between
`4 + x / log x` and `3 * (x / log x)`. The finite set in this statement uses a strict real lower
cutoff and the inclusive natural floor of the upper cutoff, so prime endpoints are counted on
the correct side.

## Main results

* `Nat.tendsto_primeCounting_mul_sub_div`: the normalized fixed-dilation interval count.
* `Nat.eventually_card_primesLE_filter_gt_mul_three_bounds`: the two-sided interval bound.

## References and provenance

The interval bound is AnalyticNumberTheoryPartI §0.10's prime-number input. The same count
asymptotic is a prerequisite of its §3.28 medium-prime-product estimate.
The scaling argument adapts the interval-prime proof `tendsto_by_squeeze` in
PrimeNumberTheoremAnd/Consequences.lean at commit `24e6efd3`, lines 438–471,
whose contributors include Matteo Cipollina. The PNT itself is supplied by Mathlib.
-/

public section

open Filter Asymptotics Finset
open scoped Topology

namespace Nat


/-- For a fixed dilation `c ≥ 1`, the normalized number of primes in `(x, c * x]` tends to
`c - 1`. The subtraction is in `ℕ`, and agrees with the interval cardinality for large `x`. -/
theorem tendsto_primeCounting_mul_sub_div {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ ↦ ((primeCounting ⌊c * x⌋₊ - primeCounting ⌊x⌋₊ : ℕ) : ℝ) /
      (x / Real.log x)) atTop (𝓝 (c - 1)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hlognorm : Tendsto (norm ∘ Real.log) atTop atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      tendsto_abs_atTop_atTop.comp Real.tendsto_log_atTop
  have hlog : (fun x : ℝ ↦ Real.log (c * x)) ~[atTop] Real.log := by
    refine (IsEquivalent.refl.const_add_of_norm_tendsto_atTop
      (c := Real.log c) hlognorm).congr_left ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.log_mul hc0.ne' hx.ne').symm
  have hscale : (fun x : ℝ ↦ c * x / Real.log (c * x)) ~[atTop]
      (fun x : ℝ ↦ c * (x / Real.log x)) := by
    convert ((IsEquivalent.refl : (fun x : ℝ ↦ c * x) ~[atTop] (fun x : ℝ ↦ c * x)).div hlog)
      using 1
    ext x
    simp only [Pi.div_apply, mul_div_assoc]
  have hpi := (Nat.isEquivalent_primeCounting.comp_tendsto
    (tendsto_id.const_mul_atTop hc0)).trans hscale
  have hden : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (_root_.div_pos (zero_lt_one.trans hx) (Real.log_pos hx)).ne'
  have herror : (fun x : ℝ ↦ (primeCounting ⌊c * x⌋₊ : ℝ) - c * (x / Real.log x)) =o[atTop]
      (fun x : ℝ ↦ x / Real.log x) :=
    hpi.isLittleO.trans_isBigO (isBigO_const_mul_self c _ _)
  have hscaled := (isLittleO_sub_mul_iff_tendsto_div hden).mp herror
  have hbase := (isEquivalent_iff_tendsto_one hden).mp Nat.isEquivalent_primeCounting
  refine (hscaled.sub hbase).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Nat.cast_sub (monotone_primeCounting (Nat.floor_mono (by nlinarith : x ≤ c * x)))]
  simp only [Pi.div_apply, sub_div]

/-- Eventually, the number of primes in `(x, 3 * x]` is between `4 + x / log x` and
`3 * (x / log x)`. The lower endpoint is strict and the upper endpoint is inclusive. -/
theorem eventually_card_primesLE_filter_gt_mul_three_bounds :
    ∀ᶠ x : ℝ in atTop,
      4 + x / Real.log x ≤ (((Nat.primesLE ⌊3 * x⌋₊).filter (fun p : ℕ ↦ x < (p : ℝ))).card : ℝ) ∧
      (((Nat.primesLE ⌊3 * x⌋₊).filter (fun p : ℕ ↦ x < (p : ℝ))).card : ℝ) ≤
        3 * (x / Real.log x) := by
  have hlim := tendsto_primeCounting_mul_sub_div (c := 3) (by norm_num)
  have hlo := (tendsto_order.mp hlim).1 (3 / 2) (by norm_num)
  have hhi := (tendsto_order.mp hlim).2 3 (by norm_num)
  filter_upwards [hlo, hhi, TauCeti.Real.tendsto_div_log_atTop.eventually_gt_atTop 8,
    eventually_ge_atTop (0 : ℝ)] with x hl hu hx hx0
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊3 * x⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono (by nlinarith : x ≤ 3 * x))
  have heq : (Nat.primesLE ⌊3 * x⌋₊).filter (fun p : ℕ ↦ x < (p : ℝ)) =
      Nat.primesLE ⌊3 * x⌋₊ \ Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_sdiff,
      Nat.le_floor_iff hx0, not_and_or, not_le]
    tauto
  rw [heq, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]
  have hpos : 0 < x / Real.log x := lt_trans (by norm_num) hx
  have hl' := (lt_div_iff₀ hpos).mp hl
  have hu' := (div_lt_iff₀ hpos).mp hu
  constructor <;> nlinarith

end Nat
