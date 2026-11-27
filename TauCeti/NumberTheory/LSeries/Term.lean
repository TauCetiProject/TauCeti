/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Basic identities and norm bounds for `LSeries.term`

This file records lightweight finite-sum identities and real-shift norm comparisons for
`LSeries.term` that do not require analytic continuation or limit theory.

## Main results

* `TauCeti.LSeries.sum_range_add_one_LSeries_term_one`: partial sums of `LSeries.term a 1` over
  `Finset.range (N + 1)` equal the ordered harmonic partial sums over `Finset.Icc 1 N`.
* `TauCeti.LSeries.norm_term_eq_exp_mul`: changing the real part of the argument rescales the norm
  of `LSeries.term a s n` by `Real.exp (Real.log n * (w.re - s.re))`.
* `TauCeti.LSeries.norm_term_le_exp_mul`: an upper bound `E` on `Real.log n * (w.re - s.re)`
  bounds `‖LSeries.term a s n‖` by `Real.exp E * ‖LSeries.term a w n‖`.
-/

public section

namespace TauCeti.LSeries

/-- Partial sums of `LSeries.term a 1` over `range (N + 1)` equal ordered harmonic sums over
`Icc 1 N`. -/
theorem sum_range_add_one_LSeries_term_one (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), LSeries.term a 1 n = ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) := by
  rw [Finset.sum_range_eq_add_Ico _ N.succ_pos, LSeries.term_zero, zero_add,
    Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
  simp only [LSeries.term_of_ne_zero' (s := 1) one_ne_zero, Complex.cpow_one]

/-- Changing the real part of the argument rescales the norm of a Dirichlet term by an
exponential in the logarithm of its index. -/
theorem norm_term_eq_exp_mul (a : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    ‖_root_.LSeries.term a s n‖ =
      Real.exp (Real.log n * (w.re - s.re)) * ‖_root_.LSeries.term a w n‖ := by
  simp only [_root_.LSeries.norm_term_eq]
  split_ifs with hn
  · simp
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos, mul_sub, Real.exp_sub]
    field_simp [Real.exp_ne_zero]

/-- An exponential bound on the real shift bounds a Dirichlet term by the corresponding term
at the reference point. -/
theorem norm_term_le_exp_mul (a : ℕ → ℂ) {s w : ℂ} {n : ℕ} {E : ℝ}
    (h : Real.log n * (w.re - s.re) ≤ E) :
    ‖_root_.LSeries.term a s n‖ ≤ Real.exp E * ‖_root_.LSeries.term a w n‖ := by
  rw [norm_term_eq_exp_mul a s w n]
  gcongr

end TauCeti.LSeries
