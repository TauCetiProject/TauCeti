/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.WeakPNT
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic

/-!
# Prime counts in fixed multiplicative intervals

For fixed nonnegative `a` and `b`, the difference between the prime counts up to `b * x` and
`a * x`, normalized by `x / log x`, tends to `b - a`. The difference is taken in `ℝ`, so reversed
endpoints are allowed. Zero and equal endpoints are included. The proof uses the qualitative
prime number theorem at both endpoints and the stability of logarithmic asymptotics under scaling.

In particular, the number of primes in `(x, 3 * x]` eventually lies between
`4 + x / log x` and `3 * (x / log x)`. The finite set in this statement uses a strict real lower
cutoff and the inclusive natural floor of the upper cutoff, so prime endpoints are counted on
the correct side.

## Main results

* `TauCeti.isEquivalent_primeCounting_floor_const_mul`: prime counts at a nonnegative fixed scale.
* `TauCeti.tendsto_primeCounting_mul_sub_mul_div`: the normalized difference at two fixed scales.
* `TauCeti.eventually_card_primesLE_filter_gt_three_mul_bounds`: the two-sided interval bound.

## References and provenance

* L. Bary-Soroker, D. Koukoulopoulos and G. Kozma,
  [*Irreducibility of random polynomials: general measures*](https://arxiv.org/abs/2007.14567),
  §3.5, proof of Theorem 2, p.25, for the two-sided interval count.

The scaling argument adapts the interval-prime proof `tendsto_by_squeeze` in
PrimeNumberTheoremAnd/Consequences.lean at commit `24e6efd3`, lines 438–471,
whose contributors include Matteo Cipollina. The PNT itself is supplied by Mathlib.
-/

public section

open Filter Asymptotics Finset Nat
open scoped Topology

namespace TauCeti


/-- Prime counts at a fixed nonnegative scale are asymptotic to `c * (x / log x)`. -/
theorem isEquivalent_primeCounting_floor_const_mul {c : ℝ} (hc : 0 ≤ c) :
    (fun x : ℝ ↦ (primeCounting ⌊c * x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ ↦ c * (x / Real.log x)) := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa only [zero_mul, Nat.floor_zero, primeCounting_zero, Nat.cast_zero] using
      (IsEquivalent.refl : (fun _ : ℝ ↦ (0 : ℝ)) ~[atTop] fun _ ↦ (0 : ℝ))
  have hlognorm : Tendsto (norm ∘ Real.log) atTop atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      tendsto_abs_atTop_atTop.comp Real.tendsto_log_atTop
  have hlog : (fun x : ℝ ↦ Real.log (c * x)) ~[atTop] Real.log := by
    refine (IsEquivalent.refl.const_add_of_norm_tendsto_atTop
      (c := Real.log c) hlognorm).congr_left ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.log_mul hc.ne' hx.ne').symm
  have hscale : (fun x : ℝ ↦ c * x / Real.log (c * x)) ~[atTop]
      (fun x : ℝ ↦ c * (x / Real.log x)) := by
    convert ((IsEquivalent.refl : (fun x : ℝ ↦ c * x) ~[atTop] (fun x : ℝ ↦ c * x)).div hlog)
      using 1
    ext x
    simp only [Pi.div_apply, mul_div_assoc]
  exact (Nat.isEquivalent_primeCounting.comp_tendsto
    (tendsto_id.const_mul_atTop hc)).trans hscale

/-- The difference of prime counts at two nonnegative fixed scales, normalized by `x / log x`,
tends to the difference of the scales. Subtraction is in `ℝ`; the scales need not be ordered. -/
theorem tendsto_primeCounting_mul_sub_mul_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun x : ℝ ↦ ((primeCounting ⌊b * x⌋₊ : ℝ) - primeCounting ⌊a * x⌋₊) /
      (x / Real.log x)) atTop (𝓝 (b - a)) := by
  have hden := TauCeti.Real.tendsto_div_log_atTop.eventually_ne_atTop 0
  have hratio (c : ℝ) (hc : 0 ≤ c) :
      Tendsto (fun x : ℝ ↦ (primeCounting ⌊c * x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 c) :=
    (isLittleO_sub_mul_iff_tendsto_div hden).mp
      ((isEquivalent_primeCounting_floor_const_mul hc).isLittleO.trans_isBigO
        (isBigO_const_mul_self c _ _))
  exact ((hratio b hb).sub (hratio a ha)).congr fun x ↦ (sub_div _ _ _).symm

/-- Eventually, the number of primes in `(x, 3 * x]` is between `4 + x / log x` and
`3 * (x / log x)`. The lower endpoint is strict and the upper endpoint is inclusive. -/
theorem eventually_card_primesLE_filter_gt_three_mul_bounds :
    ∀ᶠ x : ℝ in atTop,
      4 + x / Real.log x ≤ (((Nat.primesLE ⌊3 * x⌋₊).filter (fun p : ℕ ↦ x < (p : ℝ))).card : ℝ) ∧
      (((Nat.primesLE ⌊3 * x⌋₊).filter (fun p : ℕ ↦ x < (p : ℝ))).card : ℝ) ≤
        3 * (x / Real.log x) := by
  have hlim := tendsto_primeCounting_mul_sub_mul_div (a := 1) (b := 3)
    (by norm_num) (by norm_num)
  simp only [one_mul] at hlim
  have hlo := (tendsto_order.mp hlim).1 (3 / 2) (by norm_num)
  have hhi := (tendsto_order.mp hlim).2 3 (by norm_num)
  filter_upwards [hlo, hhi, TauCeti.Real.tendsto_div_log_atTop.eventually_gt_atTop 8,
    eventually_ge_atTop (0 : ℝ)] with x hl hu hx hx0
  have hfloor : ⌊x⌋₊ ≤ ⌊3 * x⌋₊ := Nat.floor_mono (by nlinarith : x ≤ 3 * x)
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊3 * x⌋₊ := Nat.primesLE_mono hfloor
  have heq : (Nat.primesLE ⌊3 * x⌋₊).filter (fun p : ℕ ↦ x < (p : ℝ)) =
      Nat.primesLE ⌊3 * x⌋₊ \ Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_sdiff,
      Nat.le_floor_iff hx0, not_and_or, not_le]
    tauto
  rw [heq, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting, Nat.cast_sub (Nat.monotone_primeCounting hfloor)]
  have hpos : 0 < x / Real.log x := lt_trans (by norm_num) hx
  have hl' := (lt_div_iff₀ hpos).mp hl
  have hu' := (div_lt_iff₀ hpos).mp hu
  constructor <;> nlinarith

end TauCeti
