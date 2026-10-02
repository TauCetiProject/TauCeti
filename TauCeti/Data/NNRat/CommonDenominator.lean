/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat

/-!
# Fractions of nonnegative rationals

This file relates an arbitrary fraction `a / b` representing a nonnegative rational `q` to the
reduced fraction `q.num / q.den`, and writes two nonnegative rationals over a common denominator.
These let a statement phrased through `q.num` and `q.den` be checked on any fraction of `q`.

## Main results

* `TauCeti.NNRat.num_mul_eq_of_eq_div`: `q = a / b` gives `q.num * b = a * q.den`.
* `NNRat.eq_div_den_mul_den`: `q` and `q'` as fractions over `q.den * q'.den`.
-/

public section

namespace TauCeti.NNRat

/-- **Cross-multiplying with the reduced fraction**: if `q = a / b` with `b ≠ 0`, then
`q.num * b = a * q.den`. -/
theorem num_mul_eq_of_eq_div {q : ℚ≥0} {a b : ℕ} (hb : b ≠ 0) (hq : q = a / b) :
    q.num * b = a * q.den := by
  rw [← NNRat.num_div_den q, div_eq_div_iff (by simp) (by simpa using hb)] at hq
  exact_mod_cast hq

end TauCeti.NNRat

namespace NNRat

/-- **A common denominator**: two nonnegative rationals `q` and `q'` are the fractions
`(q.num * q'.den) / (q.den * q'.den)` and `(q'.num * q.den) / (q.den * q'.den)`. -/
theorem eq_div_den_mul_den (q q' : ℚ≥0) :
    q = ((q.num * q'.den : ℕ) : ℚ≥0) / ((q.den * q'.den : ℕ) : ℚ≥0) ∧
      q' = ((q'.num * q.den : ℕ) : ℚ≥0) / ((q.den * q'.den : ℕ) : ℚ≥0) := by
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ (by simp),
    mul_comm (q.den : ℚ≥0), mul_div_mul_right _ _ (by simp), NNRat.num_div_den, NNRat.num_div_den]
  exact ⟨rfl, rfl⟩

end NNRat
