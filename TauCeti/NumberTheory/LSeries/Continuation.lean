/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Continuation from cancellation in partial sums

The Mellin transform of the inclusive coefficient partial sums defines a continuation of a
Dirichlet series. A bound `O(n ^ r)` for these complex partial sums makes the continuation
analytic on `r < re s`. Agreement with Mathlib's `LSeries` requires summability separately:
cancellation of partial sums does not imply absolute convergence of the original series.

The construction uses Mathlib's Mellin-transform differentiability theorem and the Abel
integral representation in `Mathlib.NumberTheory.LSeries.SumCoeff`.

## References

* H. Davenport, *Multiplicative Number Theory*, chapters on Dirichlet series and partial summation.
* J. Korevaar, *Tauberian Theory*, Chapter III, for the Mellin-transform continuation from partial
  sums.
-/

public section

namespace TauCeti.LSeries

open Finset Filter MeasureTheory Asymptotics Complex
open scoped Topology

/-- The continuation supplied by the Mellin transform of the inclusive partial sums.
Outside its integral convergence region this is a total function with no asserted analytic
meaning. The coefficient at zero is ignored, as in Mathlib's `LSeries`. -/
noncomputable def continuedLSeries (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * mellin (fun x : ℝ ↦ ∑ k ∈ Icc 1 ⌊x⌋₊, a k) (-s)

/-- Inclusive coefficient partial sums vanish below the first positive index. -/
theorem partialSum_eq_zero_of_lt_one (a : ℕ → ℂ) {x : ℝ} (hx : x < 1) :
    ∑ k ∈ Icc 1 ⌊x⌋₊, a k = 0 := by
  simp [Nat.floor_eq_zero.mpr hx]

/-- The Abel integral formula for the named continuation, with inclusive partial sums. -/
theorem continuedLSeries_eq_mul_integral (a : ℕ → ℂ) (s : ℂ) :
    continuedLSeries a s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, a k) * (t : ℂ) ^ (-(s + 1)) := by
  unfold continuedLSeries mellin
  congr 1
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1
  by_cases h : 1 < t
  · simp [h, zero_lt_one.trans h, smul_eq_mul, sub_eq_add_neg, add_comm, mul_comm]
  · have hzero := partialSum_eq_zero_of_lt_one a (lt_of_le_of_ne (le_of_not_gt h) ht1)
    simp [h, hzero]

/-- Inclusive coefficient partial sums are locally integrable on the positive real axis. -/
theorem locallyIntegrableOn_partialSum (a : ℕ → ℂ) :
    LocallyIntegrableOn (fun x : ℝ ↦ ∑ k ∈ Icc 1 ⌊x⌋₊, a k) (Set.Ioi 0) := by
  have h := locallyIntegrableOn_mul_sum_Icc a (m := 1) (a := (0 : ℝ)) le_rfl
    (locallyIntegrableOn_const (1 : ℂ))
  simpa using h.mono_set Set.Ioi_subset_Ici_self

/-- A polynomial bound at natural cutoffs transfers to real cutoffs by taking the floor. -/
theorem isBigO_partialSum_atTop {a : ℕ → ℂ} {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun x : ℝ ↦ ∑ k ∈ Icc 1 ⌊x⌋₊, a k) =O[atTop] fun x ↦ x ^ r := by
  have hmax : (fun x : ℝ ↦ max x 1) =ᶠ[atTop] fun x ↦ x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp [max_eq_left hx]
  have hfloor_rpow :
      (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) ^ r) ~[atTop] fun x ↦ x ^ r := by
    refine (Asymptotics.IsEquivalent.rpow (fun x : ℝ ↦ by positivity)
      (isEquivalent_nat_floor.trans_eventuallyEq hmax.symm)).trans_eventuallyEq ?_
    filter_upwards [hmax] with x hx
    simp [hx]
  exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans_isEquivalent hfloor_rpow

/-- Near zero, coefficient partial sums vanish and hence satisfy every power bound. -/
theorem isBigO_partialSum_nhdsGT_zero (a : ℕ → ℂ) (b : ℝ) :
    (fun x : ℝ ↦ ∑ k ∈ Icc 1 ⌊x⌋₊, a k) =O[𝓝[>] 0] fun x ↦ x ^ (-b) := by
  refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  filter_upwards [((eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds)] with x hx
  exact (partialSum_eq_zero_of_lt_one a hx).symm

/-- A polynomial cancellation bound makes the named continuation differentiable on the
corresponding open half-plane. No summability of the original Dirichlet series is needed. -/
theorem differentiableAt_continuedLSeries {a : ℕ → ℂ} {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) : DifferentiableAt ℂ (continuedLSeries a) s := by
  have h := mellin_differentiableAt_of_isBigO_rpow
    (a := -r) (b := (-s).re - 1) (s := -s) (locallyIntegrableOn_partialSum a)
    (by simpa using isBigO_partialSum_atTop hO)
    (by simpa using hs)
    (isBigO_partialSum_nhdsGT_zero a _) (sub_one_lt _)
  exact differentiableAt_id.mul (h.comp s differentiableAt_id.neg)

/-- The Mellin continuation is analytic strictly to the right of the partial-sum growth
exponent. -/
theorem analyticOnNhd_continuedLSeries {a : ℕ → ℂ} {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    AnalyticOnNhd ℂ (continuedLSeries a) {s | r < s.re} := by
  exact DifferentiableOn.analyticOnNhd
    (fun s hs ↦ (differentiableAt_continuedLSeries hO hs).differentiableWithinAt)
    (isOpen_lt continuous_const continuous_re)

/-- The named continuation agrees with the original series at summable points to the right of both
the partial-sum growth exponent and zero. Summability is separate from cancellation. -/
theorem continuedLSeries_eq_LSeries {a : ℕ → ℂ} {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    {s : ℂ} (hs : max r 0 < s.re) (hS : LSeriesSummable a s) :
    continuedLSeries a s = _root_.LSeries a s := by
  rw [continuedLSeries_eq_mul_integral]
  have hOmax :
      (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ max r 0 :=
    hO.trans <| Filter.Eventually.isBigO <| by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc
        ‖(n : ℝ) ^ r‖ = (n : ℝ) ^ r :=
          Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ (n : ℝ) ^ max r 0 := Real.rpow_le_rpow_of_exponent_le hn' (le_max_left _ _)
  exact (LSeries_eq_mul_integral (r := max r 0) a (le_max_right _ _) hs hS hOmax).symm

end TauCeti.LSeries
