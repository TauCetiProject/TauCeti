/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Integrating weights against the Chebyshev function

The Chebyshev function `θ` is bounded on finite intervals, so multiplying by it preserves
interval integrability. This applies to the weighted integrals arising in partial summation.
-/

public section

open MeasureTheory Set

/-- Multiplication by the Chebyshev function `θ` preserves interval integrability. -/
theorem IntervalIntegrable.mul_chebyshev_theta {w : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (hw : IntervalIntegrable w μ a b) :
    IntervalIntegrable (fun t ↦ w t * Chebyshev.theta t) μ a b := by
  rw [intervalIntegrable_iff] at hw ⊢
  refine Integrable.mul_bdd (c := Chebyshev.theta (max a b)) hw
    Chebyshev.theta_mono.measurable.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Chebyshev.theta_nonneg t)]
  exact Chebyshev.theta_mono ht.2
