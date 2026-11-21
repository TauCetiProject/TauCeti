/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Analysis.SpecialFunctions.Log.NatCastAdd
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.StepCorrection

/-!
# Exponential-step Laplace transforms of Dirichlet series

For coefficients `a : ℕ → ℂ`, the exponential-step function `t ↦ a ⌊exp t⌋₊` bridges Dirichlet
series and Laplace transforms independently of Newman's Tauberian theorem:

* on each step `[log n, log (n + 1)]`, the substitution `x = exp t` turns its Laplace integral
  into `a n ∫ x in n..n+1, x ^ (-z - 1)` (`intervalIntegral_floor_exp_mul_cexp_neg_mul`);
* summing the steps, its truncated Laplace transform at `log (N + 1)` is the partial sum of the
  Dirichlet series of `a` at `z + 1` plus the partial sum of the step correction
  (`intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ`);
* letting `N → ∞` when `a` is bounded from `n = 1` on and `0 < re z`, its Laplace transform is
  `LSeries a (z + 1) + stepCorrection a z` (`integral_floor_exp_mul_cexp_neg_mul`).

## Main declarations

* `TauCeti.LSeries.intervalIntegral_floor_exp_mul_cexp_neg_mul`: single-step Laplace integral.
* `TauCeti.LSeries.intervalIntegrable_floor_exp_mul_cexp_neg_mul`: interval integrability on a
  single step.
* `TauCeti.LSeries.intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ`: truncated Laplace
  transform over `[0, log (N + 1)]`.
* `TauCeti.LSeries.norm_floor_exp_le`: uniform bound on `t ↦ a ⌊exp t⌋₊` for `0 ≤ t`.
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

/-- **The Laplace integral over one step.** For `n ≠ 0`, the step function `t ↦ a ⌊exp t⌋₊`
equals `a n` on `(log n, log (n + 1))`, so its Laplace integral over `[log n, log (n + 1)]` is
`a n ∫ x in n..n+1, x ^ (-z - 1)`. -/
theorem intervalIntegral_floor_exp_mul_cexp_neg_mul (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    ∫ t in Real.log n..Real.log (n + 1), a ⌊Real.exp t⌋₊ * cexp (-z * t) =
      a n * ∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [intervalIntegral_ofReal_cpow_neg_sub_one hn' (by positivity),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_Ioo_of_le
    (Real.log_le_log hn' (by linarith)) fun t ht ↦ ?_
  rw [Real.floor_exp_eq_of_mem_Ioo ht]

/-- The step function `t ↦ a ⌊exp t⌋₊` times `exp (-z t)` is interval integrable on each step
`[log n, log (n + 1)]`, where for `n ≠ 0` it agrees with `a n exp (-z t)` away from the
endpoints (and for `n = 0` the interval is degenerate). -/
theorem intervalIntegrable_floor_exp_mul_cexp_neg_mul (a : ℕ → ℂ) (n : ℕ)
    (z : ℂ) : IntervalIntegrable (fun t : ℝ ↦ a ⌊Real.exp t⌋₊ * cexp (-z * t)) volume
      (Real.log n) (Real.log (n + 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  refine ((by fun_prop : Continuous fun t : ℝ ↦ a n * cexp (-z * t)).intervalIntegrable
    _ _).congr_uIoo fun t ht ↦ ?_
  rw [uIoo_of_le (Real.log_le_log hn' (by linarith))] at ht
  simp only [Real.floor_exp_eq_of_mem_Ioo ht]

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

/-- For `0 ≤ t`, the step function `t ↦ a ⌊exp t⌋₊` only takes values `a n` with `1 ≤ n`, so it
is bounded by `M` when the coefficients are bounded by `M` from `n = 1` on. -/
theorem norm_floor_exp_le (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) {t : ℝ} (ht : t ∈ Ici 0) :
    ‖a ⌊Real.exp t⌋₊‖ ≤ M :=
  hbound _ (Nat.le_floor (by simpa using Real.one_le_exp (mem_Ici.mp ht)))

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
