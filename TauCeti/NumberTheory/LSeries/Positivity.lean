/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Terms of a Dirichlet series with nonnegative coefficients at a real point

At a real point `sigma`, the terms of a Dirichlet series with nonnegative coefficients are
themselves nonnegative reals. Each term therefore equals its own norm, plain summability at `sigma`
is already absolute summability, and the value of the series is the sum of the norms of its terms.
These are the facts that turn a bound on the value `LSeries a sigma` into a bound on
`∑' n, ‖LSeries.term a sigma n‖`, which is the shape a comparison or truncation argument needs.

Mathlib's `Mathlib/NumberTheory/LSeries/Positivity.lean` records the positivity of the *values* of
such a series; the statements here are about its individual terms.

## Main declarations

* `TauCeti.LSeries.term_eq_ofReal_norm_of_nonneg`: a nonnegative coefficient makes the term at a
  real point equal to its own norm.
* `TauCeti.LSeries.summable_norm_term_of_nonneg`: for nonnegative coefficients, summability at a
  real point is absolute summability.
* `TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg`: for nonnegative coefficients, the value
  at a real point is the sum of the norms of the terms.
-/

public section

namespace TauCeti.LSeries

open scoped ComplexOrder

variable {a : ℕ → ℂ}

/-- At a real point, a nonnegative Dirichlet coefficient gives a term equal to its own norm. -/
theorem term_eq_ofReal_norm_of_nonneg {n : ℕ} (ha : 0 ≤ a n) (sigma : ℝ) :
    _root_.LSeries.term a (sigma : ℂ) n = (‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℂ) := by
  have hnn : (0 : ℂ) ≤ _root_.LSeries.term a (sigma : ℂ) n := _root_.LSeries.term_nonneg ha _
  have hre : _root_.LSeries.term a (sigma : ℂ) n =
      ((_root_.LSeries.term a (sigma : ℂ) n).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (by rw [Complex.ofReal_zero]; exact hnn)
  rw [hre, Complex.norm_real,
    Real.norm_of_nonneg (by simpa using (Complex.le_def.mp hnn).1)]

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

end TauCeti.LSeries
