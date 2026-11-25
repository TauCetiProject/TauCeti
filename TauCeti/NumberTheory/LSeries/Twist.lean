/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Twisting the coefficients of a Dirichlet series by a power of the index

Multiplying the `n`-th coefficient of a Dirichlet series by `n ^ (-z)` translates the series by
`z`: the `n`-th term becomes `f n * n ^ (-z) / n ^ s = f n / n ^ (s + z)`, so the twisted series
at `s` is the original one at `s + z`. The identity is termwise, hence needs no convergence
hypothesis; at a point where neither series converges both sides are Mathlib's junk value `0`.

The purely imaginary parameters `z = -u * I` are the ones a Hecke character twisted by
`N(I) ^ (i u)` produces. They translate the series in the imaginary (vertical) direction, so a
pole of the original series at `s = 1` becomes a pole of the twisted one at `s = 1 + i u`.

## Main results

* `TauCeti.LSeries.term_mul_natCast_cpow_neg`, `TauCeti.LSeries.LSeries_mul_natCast_cpow_neg`,
  `TauCeti.LSeries.LSeriesSummable_mul_natCast_cpow_neg_iff`, and
  `TauCeti.LSeries.LSeriesHasSum_mul_natCast_cpow_neg_iff`: twisting by `n ^ (-z)` translates
  terms, `tsum` values, summability, and `LSeriesHasSum` from `s` to `s + z`.
* `TauCeti.LSeries.term_mul_natCast_cpow`, `TauCeti.LSeries.LSeries_mul_natCast_cpow`,
  `TauCeti.LSeries.LSeriesSummable_mul_natCast_cpow_iff`, and
  `TauCeti.LSeries.LSeriesHasSum_mul_natCast_cpow_iff`: the positive-exponent versions,
  translating from `s` to `s - z`.
-/

public section

namespace TauCeti.LSeries

variable (f : ℕ → ℂ) (z s : ℂ)

/-- Twisting the `n`-th coefficient of a Dirichlet series by `n ^ (-z)` translates its `n`-th
term by `z`. -/
theorem term_mul_natCast_cpow_neg (n : ℕ) :
    LSeries.term (fun n ↦ f n * (n : ℂ) ^ (-z)) s n = LSeries.term f (s + z) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_neg]
  ring

/-- **Twisting a Dirichlet series by a power of the index translates it.** The series of the
coefficients `f n * n ^ (-z)` at `s` is the series of `f` at `s + z`. -/
theorem LSeries_mul_natCast_cpow_neg :
    LSeries (fun n ↦ f n * (n : ℂ) ^ (-z)) s = LSeries f (s + z) :=
  tsum_congr (term_mul_natCast_cpow_neg f z s)

/-- Twisting by `n ^ (-z)` translates absolute summability from `s` to `s + z`. -/
theorem LSeriesSummable_mul_natCast_cpow_neg_iff :
    LSeriesSummable (fun n ↦ f n * (n : ℂ) ^ (-z)) s ↔ LSeriesSummable f (s + z) := by
  simp only [LSeriesSummable, funext (term_mul_natCast_cpow_neg f z s)]

/-- Twisting by `n ^ (-z)` translates `LSeriesHasSum` from `s` to `s + z`. -/
theorem LSeriesHasSum_mul_natCast_cpow_neg_iff (a : ℂ) :
    LSeriesHasSum (fun n ↦ f n * (n : ℂ) ^ (-z)) s a ↔ LSeriesHasSum f (s + z) a := by
  simp only [LSeriesHasSum, funext (term_mul_natCast_cpow_neg f z s)]

/-- Twisting the `n`-th coefficient of a Dirichlet series by `n ^ z` translates its `n`-th term
to `s - z`. -/
theorem term_mul_natCast_cpow (n : ℕ) :
    LSeries.term (fun n ↦ f n * (n : ℂ) ^ z) s n = LSeries.term f (s - z) n := by
  simpa [sub_eq_add_neg] using term_mul_natCast_cpow_neg f (-z) s n

/-- The Dirichlet series of `f n * n ^ z` at `s` equals that of `f` at `s - z`. -/
theorem LSeries_mul_natCast_cpow :
    LSeries (fun n ↦ f n * (n : ℂ) ^ z) s = LSeries f (s - z) :=
  tsum_congr (term_mul_natCast_cpow f z s)

/-- Twisting by `n ^ z` translates absolute summability from `s` to `s - z`. -/
theorem LSeriesSummable_mul_natCast_cpow_iff :
    LSeriesSummable (fun n ↦ f n * (n : ℂ) ^ z) s ↔ LSeriesSummable f (s - z) := by
  simp only [LSeriesSummable, funext (term_mul_natCast_cpow f z s)]

/-- Twisting by `n ^ z` translates `LSeriesHasSum` from `s` to `s - z`. -/
theorem LSeriesHasSum_mul_natCast_cpow_iff (a : ℂ) :
    LSeriesHasSum (fun n ↦ f n * (n : ℂ) ^ z) s a ↔ LSeriesHasSum f (s - z) a := by
  simp only [LSeriesHasSum, funext (term_mul_natCast_cpow f z s)]

end TauCeti.LSeries
