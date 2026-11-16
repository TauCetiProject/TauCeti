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
abscissa of absolute convergence. We also record the triangle-inequality majorant
`‖LSeries a s‖ ≤ (LSeries a s.re).re` (valid unconditionally, since both sides vanish off the
summability set) and strict antitonicity of `x ↦ (LSeries a x).re` on the summability ray when
some coefficient at `n ≥ 2` is positive.

## Main declarations

* `TauCeti.LSeries.term_eq_ofReal_norm_of_nonneg`: a nonnegative coefficient makes the term at a
  real point equal to its own norm.
* `TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg`: for nonnegative coefficients, the value
  at a real point is the sum of the norms of the terms.
* `TauCeti.LSeries.norm_LSeries_le_re_of_nonneg`: for nonnegative coefficients,
  `‖LSeries a s‖ ≤ (LSeries a s.re).re` for all `s : ℂ`.
* `TauCeti.LSeries.strictAntiOn_re_of_exists_pos`: if some coefficient at `n ≥ 2` is positive,
  `x ↦ (LSeries a x).re` is strictly antitone on `{x : ℝ | LSeriesSummable a x}`.
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

/-- For nonnegative coefficients, the norm of `LSeries a s` at any complex point `s` is bounded by
the real part of `LSeries a` at `s.re`. No summability hypothesis is needed: when the series is not
summable at `s`, it is not summable at `s.re` either, so both sides vanish. -/
theorem norm_LSeries_le_re_of_nonneg (ha : 0 ≤ a) (s : ℂ) :
    ‖LSeries a s‖ ≤ (LSeries a s.re).re := by
  by_cases hs : LSeriesSummable a s
  · have hs' : Summable fun n ↦ ‖_root_.LSeries.term a s n‖ := summable_norm_iff.mpr hs
    have hterm (n : ℕ) : ‖_root_.LSeries.term a s n‖ = ‖_root_.LSeries.term a (s.re : ℂ) n‖ := by
      simp [_root_.LSeries.norm_term_eq]
    calc
      ‖LSeries a s‖ ≤ ∑' n, ‖_root_.LSeries.term a s n‖ := norm_tsum_le_tsum_norm hs'
      _ = ∑' n, ‖_root_.LSeries.term a (s.re : ℂ) n‖ := tsum_congr hterm
      _ = (LSeries a s.re).re := by
        rw [LSeries_eq_ofReal_tsum_norm_of_nonneg ha s.re, Complex.ofReal_re]
  · have hs_re : ¬ LSeriesSummable a (s.re : ℂ) := fun h ↦ hs (h.of_re_le_re (by simp))
    rw [_root_.LSeries.eq_zero_of_not_LSeriesSummable a s hs,
      _root_.LSeries.eq_zero_of_not_LSeriesSummable a (s.re : ℂ) hs_re]
    simp

/-- For nonnegative coefficients with at least one positive value at an index `n ≥ 2`, the real
function `x ↦ (LSeries a x).re` is strictly antitone on the set of real points of summability. -/
theorem strictAntiOn_re_of_exists_pos (ha : 0 ≤ a) (hpos : ∃ n ≥ 2, 0 < a n) :
    StrictAntiOn (fun x : ℝ ↦ (LSeries a x).re) {x : ℝ | LSeriesSummable a x} := by
  intro x hx y hy hxy
  obtain ⟨n, hn2, han⟩ := hpos
  have hx' : Summable fun m ↦ ‖_root_.LSeries.term a (x : ℂ) m‖ := summable_norm_iff.mpr hx
  have hy' : Summable fun m ↦ ‖_root_.LSeries.term a (y : ℂ) m‖ := summable_norm_iff.mpr hy
  have hle (m : ℕ) : ‖_root_.LSeries.term a (y : ℂ) m‖ ≤ ‖_root_.LSeries.term a (x : ℂ) m‖ :=
    _root_.LSeries.norm_term_le_of_re_le_re a (by simpa using hxy.le) m
  have hlt : ‖_root_.LSeries.term a (y : ℂ) n‖ < ‖_root_.LSeries.term a (x : ℂ) n‖ := by
    have hn0 : n ≠ 0 := by omega
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
    simp only [_root_.LSeries.norm_term_eq, hn0, ↓reduceIte, Complex.ofReal_re]
    exact div_lt_div_of_pos_left (norm_pos_iff.mpr han.ne') (by positivity)
      (Real.rpow_lt_rpow_of_exponent_lt hn1 hxy)
  dsimp only
  rw [LSeries_eq_ofReal_tsum_norm_of_nonneg ha x, LSeries_eq_ofReal_tsum_norm_of_nonneg ha y,
    Complex.ofReal_re, Complex.ofReal_re]
  exact hy'.tsum_lt_tsum hle hlt hx'

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
