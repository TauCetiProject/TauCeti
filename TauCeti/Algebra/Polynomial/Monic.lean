/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic

/-!
# Monic polynomials

For `n ≠ 0` the polynomial `Xⁿ + 1` is monic over any semiring (`Polynomial.monic_X_pow_add_one`).
This is the analogue for `+` of Mathlib's `Polynomial.monic_X_pow_sub_one`.
-/

public section

namespace Polynomial

/-- `Xⁿ + 1` is monic for `n ≠ 0`. -/
theorem monic_X_pow_add_one {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) :
    (X ^ n + 1 : R[X]).Monic := by
  rw [← C_1]
  exact monic_X_pow_add_C 1 hn

end Polynomial

end
