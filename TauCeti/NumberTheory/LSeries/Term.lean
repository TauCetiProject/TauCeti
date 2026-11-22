/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Finite partial sums of `LSeries.term`

This file records lightweight finite-sum identities for `LSeries.term` that do not require
analytic continuation or limit theory.

## Main results

* `TauCeti.LSeries.sum_range_add_one_LSeries_term_one`: partial sums of `LSeries.term a 1` over
  `Finset.range (N + 1)` equal the ordered harmonic partial sums over `Finset.Icc 1 N`.
-/

public section

namespace TauCeti.LSeries

/-- Partial sums of `LSeries.term a 1` over `range (N + 1)` equal ordered harmonic sums over
`Icc 1 N`. -/
theorem sum_range_add_one_LSeries_term_one (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), LSeries.term a 1 n = ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) := by
  rw [Finset.sum_range_eq_add_Ico _ N.succ_pos, LSeries.term_zero, zero_add,
    Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [LSeries.term_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1),
    Complex.cpow_one]

end TauCeti.LSeries
