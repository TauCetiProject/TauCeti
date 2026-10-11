/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.LSeries.Positivity

/-!
# Positivity for nonnegative Dirichlet series

This file records the positivity of an `LSeries` at every point of absolute convergence when at
least one coefficient on the positive integers is positive. It extends Mathlib's
`LSeries.positive`, which assumes positivity of the first coefficient, and is useful in arguments
about the boundary of convergence.
-/

public section

open scoped ComplexOrder
open Complex

namespace LSeries

/-- A Dirichlet series with nonnegative real coefficients is positive to the right of its
abscissa of absolute convergence whenever some coefficient at a positive integer is positive. -/
lemma positive_of_exists_pos {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hpos : ∃ n ≠ 0, 0 < a n) {x : ℝ} (hx : abscissaOfAbsConv a < x) :
    0 < LSeries a x := by
  obtain ⟨n, hn, hₙ⟩ := hpos
  rw [LSeries]
  refine Summable.tsum_pos
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa only [ofReal_re] using hx))
    (fun n ↦ term_nonneg (ha n) x) n ?_
  exact term_pos hn hₙ x

end LSeries
