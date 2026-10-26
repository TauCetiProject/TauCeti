/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Conjugating Dirichlet series

Coefficientwise complex conjugation reflects a Dirichlet series across the real axis. This file
records the termwise identity, its effect on absolute convergence and sums, and invariance of the
absolute-convergence abscissa. These results apply to arbitrary complex coefficients, including
local Euler factors. The value identity also holds at nonsummable inputs, where both series have
Mathlib's totalized value zero.

The construction uses Mathlib's `LSeries.term` and the continuous-star infinite-sum API.
-/

public section

namespace TauCeti.LSeries

/-- Conjugating the coefficients and the argument conjugates each Dirichlet-series term. -/
@[simp]
theorem term_star (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (star f) ((starRingEnd ℂ) s) n = star (LSeries.term f s n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hpow := Complex.cpow_conj (n : ℂ) s
    (by simpa only [Complex.natCast_arg] using Real.pi_pos.ne)
  simpa only [LSeries.term_of_ne_zero hn, Pi.star_apply, star_div₀,
    Complex.star_def, Complex.conj_natCast] using congrArg (fun z ↦ star (f n) / z) hpow

/-- Reflection preserves absolute convergence of a Dirichlet series. -/
@[simp]
theorem LSeriesSummable_star_iff (f : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (star f) ((starRingEnd ℂ) s) ↔ LSeriesSummable f s := by
  simp only [LSeriesSummable, funext (term_star f s), summable_star_iff]

/-- Conjugating coefficients and reflecting the argument conjugates a prescribed
Dirichlet-series sum. -/
@[simp]
theorem LSeriesHasSum_star_iff (f : ℕ → ℂ) (s a : ℂ) :
    LSeriesHasSum (star f) ((starRingEnd ℂ) s) ((starRingEnd ℂ) a) ↔
      LSeriesHasSum f s a := by
  simpa only [LSeriesHasSum, funext (term_star f s), Complex.star_def] using
    (Complex.hasSum_conj' (f := LSeries.term f s) (x := a))

/-- The totalized value of the conjugate Dirichlet series is the conjugate value. No convergence
hypothesis is needed. -/
@[simp]
theorem LSeries_star (f : ℕ → ℂ) (s : ℂ) :
    LSeries (star f) ((starRingEnd ℂ) s) = star (LSeries f s) := by
  simp only [LSeries, funext (term_star f s), tsum_star]

/-- Coefficientwise conjugation does not change the abscissa of absolute convergence. -/
@[simp]
theorem abscissaOfAbsConv_star (f : ℕ → ℂ) :
    LSeries.abscissaOfAbsConv (star f) = LSeries.abscissaOfAbsConv f := by
  simp only [LSeries.abscissaOfAbsConv]
  congr 2
  ext x
  simpa only [Set.mem_ofPred_eq, Complex.star_def, Complex.conj_ofReal] using
    LSeriesSummable_star_iff f x

end TauCeti.LSeries
