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

* `NNRat.eq_div_iff_num_mul_eq_mul_den`: for `b ≠ 0`, `q = a / b` iff `q.num * b = a * q.den`.
* `NNRat.natCast_mul_eq_div`: `n * q` as the fraction `(n * q.num) / q.den`.
* `NNRat.eq_div_den_mul_den`: `q` and `q'` as fractions over `q.den * q'.den`.
-/

public section

namespace NNRat

/-- **Cross-multiplying with the reduced fraction**: for `b ≠ 0`, `q = a / b` exactly when
`q.num * b = a * q.den`. -/
theorem eq_div_iff_num_mul_eq_mul_den {q : ℚ≥0} {a b : ℕ} (hb : b ≠ 0) :
    q = a / b ↔ q.num * b = a * q.den := by
  rw [← divNat_inj q.den_ne_zero hb, num_divNat_den, divNat_eq_div]

/-- **Scaling the reduced fraction**: `n * q` is the fraction `(n * q.num) / q.den`. -/
theorem natCast_mul_eq_div (q : ℚ≥0) (n : ℕ) :
    (n : ℚ≥0) * q = ((n * q.num : ℕ) : ℚ≥0) / (q.den : ℚ≥0) := by
  rw [Nat.cast_mul, mul_div_assoc, num_div_den]

/-- **A common denominator**: two nonnegative rationals `q` and `q'` are the fractions
`(q.num * q'.den) / (q.den * q'.den)` and `(q'.num * q.den) / (q.den * q'.den)`. -/
theorem eq_div_den_mul_den (q q' : ℚ≥0) :
    q = ((q.num * q'.den : ℕ) : ℚ≥0) / ((q.den * q'.den : ℕ) : ℚ≥0) ∧
      q' = ((q'.num * q.den : ℕ) : ℚ≥0) / ((q.den * q'.den : ℕ) : ℚ≥0) := by
  constructor <;> rw [eq_div_iff_num_mul_eq_mul_den (mul_ne_zero q.den_ne_zero q'.den_ne_zero)] <;>
    ac_rfl

end NNRat
