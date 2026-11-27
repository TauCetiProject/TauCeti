/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic

/-!
# Regularity of `1 - X ^ n`

For `n ≠ 0`, the polynomial `1 - X ^ n` is minus the monic polynomial `X ^ n - 1`, so it is not a
zero divisor in `R[X]` over any ring `R`. Equations of polynomials multiplied by a power of
`1 - X ^ n` can therefore be cancelled.

## Main results

* `Polynomial.isRegular_one_sub_X_pow`: `1 - X ^ n` is regular in `R[X]` when `n ≠ 0`.
-/

public section

namespace Polynomial

/-- For `n ≠ 0`, `1 - X ^ n` is not a zero divisor in `R[X]`: it is minus the monic polynomial
`X ^ n - 1`. -/
theorem isRegular_one_sub_X_pow {R : Type*} [Ring R] {n : ℕ} (hn : n ≠ 0) :
    IsRegular (1 - X ^ n : R[X]) := by
  rw [← neg_sub, neg_eq_neg_one_mul]
  exact isUnit_one.neg.isRegular.mul (monic_X_pow_sub_one hn).isRegular

end Polynomial
