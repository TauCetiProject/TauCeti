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
themselves nonnegative reals. Each term therefore equals its own norm, and the value of the series
is the sum of the norms of its terms. This is the fact that turns a bound on the value
`LSeries a sigma` into a bound on `∑' n, ‖LSeries.term a sigma n‖`, which is the shape a comparison
or truncation argument needs. (Summability of that norm series needs no positivity: in `ℂ`, plain
summability is already absolute summability, by Mathlib's `summable_norm_iff`.)

Mathlib's `Mathlib/NumberTheory/LSeries/Positivity.lean` records the positivity of the *values* of
such a series under the assumption that the first coefficient is positive. Here we only ask that
some coefficient at a positive index be positive: the value is then positive at every real point
where the series is summable, in particular at every real point strictly to the right of the
abscissa of absolute convergence.

## Main declarations

* `TauCeti.LSeries.term_eq_ofReal_norm_of_nonneg`: a nonnegative coefficient makes the term at a
  real point equal to its own norm.
* `TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg`: for nonnegative coefficients, the value
  at a real point is the sum of the norms of the terms.
* `TauCeti.LSeries.re_term_of_ne_zero`: the real part of a term at a real point is
  `Re (a n) / n ^ x`.
* `TauCeti.LSeries.strictAntiOn_re_of_exists_pos`: if the coefficients at indices `n ≥ 2` have
  nonnegative real parts, one of them positive, then `x ↦ Re (LSeries a x)` is strictly antitone
  on the real points of summability.
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

/-- For nonnegative coefficients, the value of the Dirichlet series at a real point is the sum of
the norms of its terms. -/
theorem LSeries_eq_ofReal_tsum_norm_of_nonneg (ha : 0 ≤ a) (sigma : ℝ) :
    LSeries a (sigma : ℂ) = ((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ term_eq_ofReal_norm_of_nonneg (ha n) sigma

/-- The real part of a Dirichlet term at a real point. -/
theorem re_term_of_ne_zero (a : ℕ → ℂ) (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (_root_.LSeries.term a (x : ℂ) n).re = (a n).re / (n : ℝ) ^ x := by
  have hcast : (n : ℂ) ^ (x : ℂ) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  rw [_root_.LSeries.term_of_ne_zero hn, hcast, Complex.div_ofReal_re]

/-- If the coefficients at indices `n ≥ 2` have nonnegative real parts, one of them positive, then
`x ↦ Re (LSeries a x)` is strictly antitone on the set of real points of summability: the real
part of the term at `n ≥ 2` is `Re (a n) / n ^ x`, nonincreasing in `x` and strictly decreasing at
that index, while the terms at `0` and `1` do not depend on `x`. -/
theorem strictAntiOn_re_of_exists_pos (ha : ∀ n ≥ 2, 0 ≤ (a n).re)
    (hpos : ∃ n ≥ 2, 0 < (a n).re) :
    StrictAntiOn (fun x : ℝ ↦ (LSeries a x).re) {x : ℝ | LSeriesSummable a x} := by
  intro x hx y hy hxy
  obtain ⟨n₀, hn₀, han₀⟩ := hpos
  have hle (n : ℕ) :
      (_root_.LSeries.term a (y : ℂ) n).re ≤ (_root_.LSeries.term a (x : ℂ) n).re := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · simp
    · rw [re_term_of_ne_zero a y (by omega : n ≠ 0), re_term_of_ne_zero a x (by omega : n ≠ 0)]
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      exact div_le_div_of_nonneg_left (ha n hn) (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_le_rpow_of_exponent_le h1 hxy.le)
  have hlt : (_root_.LSeries.term a (y : ℂ) n₀).re < (_root_.LSeries.term a (x : ℂ) n₀).re := by
    rw [re_term_of_ne_zero a y (by omega : n₀ ≠ 0),
      re_term_of_ne_zero a x (by omega : n₀ ≠ 0)]
    have h1 : (1 : ℝ) < n₀ := by exact_mod_cast (by omega : 1 < n₀)
    exact div_lt_div_of_pos_left han₀ (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_lt_rpow_of_exponent_lt h1 hxy)
  simp only [LSeries]
  exact hasSum_lt hle hlt (Complex.hasSum_re hy.hasSum) (Complex.hasSum_re hx.hasSum)

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
