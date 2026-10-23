/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Dirichlet series with nonnegative coefficients at a real point

At a real point `sigma`, the terms of a Dirichlet series with nonnegative coefficients are
themselves nonnegative reals. Each term therefore equals its own norm, plain summability at `sigma`
is already absolute summability, and the value of the series is the sum of the norms of its terms.
These are the facts that turn a bound on the value `LSeries a sigma` into a bound on
`∑' n, ‖LSeries.term a sigma n‖`, which is the shape a comparison or truncation argument needs.

Mathlib's `Mathlib/NumberTheory/LSeries/Positivity.lean` records the positivity of the *values* of
such a series under the assumption that the first coefficient is positive. Here we only ask that
some coefficient at a positive index be positive: the value is then positive at every real point
where the series is summable, in particular at every real point strictly to the right of the
abscissa of absolute convergence.

## Main declarations

* `TauCeti.LSeries.term_eq_ofReal_norm_of_nonneg`: a nonnegative coefficient makes the term at a
  real point equal to its own norm.
* `TauCeti.LSeries.summable_norm_term_of_nonneg`: for nonnegative coefficients, summability at a
  real point is absolute summability.
* `TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg`: for nonnegative coefficients, the value
  at a real point is the sum of the norms of the terms.
* `TauCeti.LSeries.positive_of_exists_pos_of_summable`: for nonnegative coefficients, one of which
  at a positive index is positive, the value at a real point of summability is positive.
* `TauCeti.LSeries.positive_of_exists_pos`: the same conclusion at every real point strictly to the
  right of the abscissa of absolute convergence.
-/

public section

namespace TauCeti.LSeries

open scoped ComplexOrder

variable {a : ℕ → ℂ}

/-- At a real point, a nonnegative Dirichlet coefficient gives a term equal to its own norm. -/
theorem term_eq_ofReal_norm_of_nonneg {n : ℕ} (ha : 0 ≤ a n) (sigma : ℝ) :
    _root_.LSeries.term a (sigma : ℂ) n = (‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℂ) :=
  Complex.eq_coe_norm_of_nonneg (_root_.LSeries.term_nonneg ha sigma)

/-- For nonnegative coefficients, summability at a real point is absolute summability. -/
theorem summable_norm_term_of_nonneg (ha : 0 ≤ a) {sigma : ℝ}
    (h : LSeriesSummable a sigma) :
    Summable fun n : ℕ ↦ ‖_root_.LSeries.term a (sigma : ℂ) n‖ := by
  rw [← Complex.summable_ofReal]
  exact h.congr fun n ↦ term_eq_ofReal_norm_of_nonneg (ha n) sigma

/-- For nonnegative coefficients, the value of the Dirichlet series at a real point is the sum of
the norms of its terms. -/
theorem LSeries_eq_ofReal_tsum_norm_of_nonneg (ha : 0 ≤ a) (sigma : ℝ) :
    LSeries a (sigma : ℂ) = ((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ term_eq_ofReal_norm_of_nonneg (ha n) sigma

/-- A Dirichlet series with nonnegative coefficients, one of which at a positive index is positive,
has a positive value at every real point where it is summable. -/
theorem positive_of_exists_pos_of_summable (ha : 0 ≤ a) (hpos : ∃ n ≠ 0, 0 < a n) {x : ℝ}
    (hx : LSeriesSummable a x) :
    0 < LSeries a x := by
  obtain ⟨n, hn, hₙ⟩ := hpos
  exact hx.tsum_pos (fun m ↦ _root_.LSeries.term_nonneg (ha m) x) n
    (_root_.LSeries.term_pos hn hₙ x)

/-- A Dirichlet series with nonnegative coefficients, one of which at a positive index is positive,
has a positive value at every real point strictly to the right of its abscissa of absolute
convergence. This generalizes Mathlib's `LSeries.positive`, which asks for `0 < a 1`. -/
theorem positive_of_exists_pos (ha : 0 ≤ a) (hpos : ∃ n ≠ 0, 0 < a n) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) :
    0 < LSeries a x :=
  positive_of_exists_pos_of_summable ha hpos <|
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa only [Complex.ofReal_re] using hx)

end TauCeti.LSeries
