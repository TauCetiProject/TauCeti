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
`x ^ (1 / q)` of `x : ℝ≥0` is `(x ^ q.den) ^ (1 / q.num)`. This turns an inequality against
`x ^ (1 / q)` into one between natural-number powers, via `NNReal.rpow_inv_le_iff` and
`NNReal.le_rpow_inv_iff`.

## Main results

* `NNReal.rpow_inv_nnratCast`: `x ^ (1 / q) = (x ^ q.den) ^ (1 / q.num)`.
-/

public section

open scoped NNReal

namespace NNReal

/-- Writing `q = a / b` in lowest terms, `x ^ (1 / q) = (x ^ b) ^ (1 / a)`. -/
theorem rpow_inv_nnratCast (x : ℝ≥0) (q : ℚ≥0) :
    x ^ ((q : ℝ)⁻¹) = (x ^ q.den) ^ ((q.num : ℝ)⁻¹) := by
  rw [NNRat.cast_def, inv_div, div_eq_mul_inv, NNReal.rpow_mul, NNReal.rpow_natCast]

end NNReal
