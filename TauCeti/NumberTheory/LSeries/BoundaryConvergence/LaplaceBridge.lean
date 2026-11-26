/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.StepCorrection
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.LaplaceTransform.ExponentialStep
import TauCeti.Analysis.SpecialFunctions.Log.NatCastAdd
import TauCeti.NumberTheory.LSeries.Term

/-!
# Exponential-step Laplace transforms of Dirichlet series

For coefficients `a : ℕ → ℂ`, the exponential-step function `t ↦ a ⌊exp t⌋₊` bridges Dirichlet
series and Laplace transforms independently of Newman's Tauberian theorem (building on the
single-step integrals in `TauCeti.Analysis.LaplaceTransform.ExponentialStep`):

* summing the steps, its truncated Laplace transform at `log (N + 1)` is the partial sum of the
  Dirichlet series of `a` at `z + 1` plus the partial sum of the step correction
  (`intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ`, with unweighted `z = 0` specialization
  `intervalIntegral_floor_exp_log_succ`);
* letting `N → ∞` when `a` is bounded from `n = 1` on and `0 < re z`, its Laplace transform is
  `LSeries a (z + 1) + stepCorrection a z` (`integral_floor_exp_mul_cexp_neg_mul`).

## Main declarations

* `TauCeti.LSeries.intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ`: truncated Laplace
  transform over `[0, log (N + 1)]`.
* `TauCeti.LSeries.intervalIntegral_floor_exp_log_succ`: unweighted `z = 0` specialization over
  `[0, log (N + 1)]`.
* `TauCeti.LSeries.integral_floor_exp_mul_cexp_neg_mul`: full Laplace–Dirichlet identity on
  `0 < re z`.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter MeasureTheory Set
open scoped Topology Complex Interval

namespace TauCeti.LSeries

variable {a : ℕ → ℂ} {M : ℝ} {z : ℂ}

/-- **The truncated Laplace transform of the step function.** For every `N`, the Laplace integral
of `t ↦ a ⌊exp t⌋₊` over `[0, log (N + 1)]` is the partial sum up to `N` of the Dirichlet series
of `a` at `z + 1` plus that of the step correction. -/
theorem intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    ∫ t in (0 : ℝ)..Real.log (N + 1), a ⌊Real.exp t⌋₊ * cexp (-z * t) =
      ∑ n ∈ Finset.range (N + 1), (LSeries.term a (z + 1) n + stepCorrectionTerm a n z) := by
  -- the steps `[log (k + 1), log (k + 2)]`, `k < N`, partition `[0, log (N + 1)]`
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ ↦ a ⌊Real.exp t⌋₊ * cexp (-z * t)) (μ := volume)
    (a := fun k : ℕ ↦ Real.log (k + 1)) (n := N) fun k _ ↦ by
      simpa using intervalIntegrable_floor_exp_mul_cexp_neg_mul a k.succ z
  simp only [Nat.cast_zero, zero_add, Real.log_one] at h
  rw [← h, Finset.sum_range_succ', LSeries.term_zero, stepCorrectionTerm_zero, Pi.zero_apply,
    add_zero, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h₁ := intervalIntegral_floor_exp_mul_cexp_neg_mul a k.succ_ne_zero z
  push_cast at h₁ ⊢
  rw [h₁, LSeries.term_of_ne_zero k.succ_ne_zero, stepCorrectionTerm_of_ne_zero a k.succ_ne_zero,
    div_eq_mul_inv, ← Complex.cpow_neg, neg_add', ← mul_add]
  push_cast
  ring

/-- **The unweighted truncated integral of the step function.** Specializing
`intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ` to `z = 0` separates the ordered harmonic
partial sum `∑ n ∈ Finset.Icc 1 N, a n / n` from the `z = 0` step correction. -/
theorem intervalIntegral_floor_exp_log_succ (a : ℕ → ℂ) (N : ℕ) :
    ∫ t in (0 : ℝ)..Real.log (N + 1), a ⌊Real.exp t⌋₊ =
      (∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ)) +
        ∑ n ∈ Finset.range (N + 1), stepCorrectionTerm a n 0 := by
  have h := intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ a N 0
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one, zero_add,
    Finset.sum_add_distrib, sum_range_add_one_LSeries_term_one] at h
  exact h

/-- **The Laplace transform of the step function.** For coefficients bounded from `n = 1` on and
`0 < re z`, the Laplace transform of `t ↦ a ⌊exp t⌋₊` is `LSeries a (z + 1) + stepCorrection a z`.
-/
theorem integral_floor_exp_mul_cexp_neg_mul (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) (hz : 0 < z.re) :
    ∫ t in Ici (0 : ℝ), a ⌊Real.exp t⌋₊ * cexp (-z * t) =
      LSeries a (z + 1) + stepCorrection a z := by
  have hint := integrableOn_mul_cexp_neg_mul
    (measurable_from_nat.comp Real.measurable_exp.nat_floor).aestronglyMeasurable
    (fun t ht ↦ norm_floor_exp_le hbound ht) hz
  have hL : LSeriesSummable a (z + 1) :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n hn ↦ hbound n (Nat.one_le_iff_ne_zero.mpr hn))
      (by simpa using hz)
  have hsum := (hL.LSeriesHasSum.add (hasSum_stepCorrection hbound (by linarith))).tendsto_sum_nat
  rw [integral_Ici_eq_integral_Ioi]
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0
    ((integrableOn_Ici_iff_integrableOn_Ioi).mp hint) (Real.tendsto_log_natCast_add_atTop 1)) ?_
  simp_rw [intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ]
  exact hsum.comp (tendsto_add_atTop_nat 1)

end TauCeti.LSeries
