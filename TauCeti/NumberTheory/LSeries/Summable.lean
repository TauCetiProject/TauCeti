/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.AbelSummation

/-!
# Summability at `s = 1` of a logarithmically damped Dirichlet series

A Dirichlet series whose coefficients have `O(t log t)` partial sums need not converge on the line
`Re s = 1`, but it does converge there once each coefficient is weighted by a factor of size
`O((1 + log n) ^ (-3))`: two of the three logarithms pay for the growth of the partial sums, and
the Abel-summation bound `TauCeti.summable_div_mul_one_add_log_cube` supplies the remaining one.

Such a weight arises whenever a Dirichlet series is tested against a smooth compactly supported
function, whose Fourier transform decays faster than every power.

## Main declarations

* `TauCeti.LSeries.LSeriesSummable_mul_of_norm_le`: an `O((1 + log n) ^ (-3))` weighting of
  coefficients with `O(t log t)` partial sums has a Dirichlet series converging at `s = 1`.
-/

public section

namespace TauCeti.LSeries

open Asymptotics Filter

variable {a W : ℕ → ℂ} {D : ℝ}

/-- Weighting coefficients with an `O((1 + log n) ^ (-3))` factor leaves a Dirichlet series that
converges at `s = 1`, as soon as the partial sums of `‖a‖` are `O(t log t)`. -/
theorem LSeriesSummable_mul_of_norm_le
    (hgrowth : (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[atTop] fun t : ℝ ↦ t * Real.log t)
    (hW : ∀ᶠ n : ℕ in atTop, ‖W n‖ ≤ D / (1 + Real.log n) ^ 3) :
    LSeriesSummable (fun n ↦ a n * W n) 1 := by
  have hD : 0 ≤ D := by
    obtain ⟨n, hn, hn1⟩ := (hW.and (eventually_ge_atTop 1)).exists
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hu : (0 : ℝ) < 1 + Real.log n := by
      have := Real.log_nonneg hn1'
      linarith
    have h0 : (0 : ℝ) ≤ D / (1 + Real.log n) ^ 3 := le_trans (norm_nonneg _) hn
    rwa [le_div_iff₀ (pow_pos hu 3), zero_mul] at h0
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ ↦ D * (‖a n‖ / (n * (1 + Real.log n) ^ 3)))
    ((summable_div_mul_one_add_log_cube (fun n ↦ norm_nonneg (a n)) hgrowth).mul_left D) ?_
  filter_upwards [hW, eventually_ge_atTop 1] with n hn hn1
  have hn0 : n ≠ 0 := by omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 + Real.log n := by
    have := Real.log_nonneg hn1'
    linarith
  rw [_root_.LSeries.term_of_ne_zero hn0, Complex.cpow_one, norm_div, norm_mul,
    Complex.norm_natCast]
  calc ‖a n‖ * ‖W n‖ / (n : ℝ)
      ≤ ‖a n‖ * (D / (1 + Real.log n) ^ 3) / (n : ℝ) := by gcongr
    _ = D * (‖a n‖ / ((n : ℝ) * (1 + Real.log n) ^ 3)) := by
        have hn' : (n : ℝ) ≠ 0 := hnpos.ne'
        have hu' : (1 : ℝ) + Real.log n ≠ 0 := hu.ne'
        field_simp

end TauCeti.LSeries
