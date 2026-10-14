/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Nonnegative real powers with nonnegative rational exponents

Writing a nonnegative rational `q` as the reduced fraction `q.num / q.den`, the real power
`x ^ (1 / q)` of `x : ℝ≥0` is `(x ^ q.den) ^ (1 / q.num)`. For `q ≠ 0`, so that `q.num > 0`, this
turns an inequality against `x ^ (1 / q)` into one between natural-number powers, via
`NNReal.rpow_inv_le_iff` and `NNReal.le_rpow_inv_iff`.

## Main results

* `NNReal.rpow_inv_nnratCast`: `x ^ (1 / q) = (x ^ q.den) ^ (1 / q.num)`.
* `NNReal.rpow_inv_nnratCast_pow_num`: for `q ≠ 0`, `(x ^ (1 / q)) ^ q.num = x ^ q.den`.
-/

public section

open scoped NNReal

namespace NNReal

/-- Writing `q = a / b` in lowest terms, `x ^ (1 / q) = (x ^ b) ^ (1 / a)`. -/
theorem rpow_inv_nnratCast (x : ℝ≥0) (q : ℚ≥0) :
    x ^ ((q : ℝ)⁻¹) = (x ^ q.den) ^ ((q.num : ℝ)⁻¹) := by
  rw [NNRat.cast_def, inv_div, div_eq_mul_inv, NNReal.rpow_mul, NNReal.rpow_natCast]

/-- Writing `q = a / b ≠ 0` in lowest terms, `ρ = x ^ (1 / q)` solves `ρ ^ a = x ^ b`. -/
theorem rpow_inv_nnratCast_pow_num (x : ℝ≥0) {q : ℚ≥0} (hq : q ≠ 0) :
    (x ^ ((q : ℝ)⁻¹)) ^ q.num = x ^ q.den := by
  rw [rpow_inv_nnratCast, rpow_inv_natCast_pow _ (NNRat.num_ne_zero.mpr hq)]

end NNReal
