/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Basic.Sign.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Signs of two scaled powers

Multiplying `lc ^ a` and `lc ^ b` by a common factor `u` with `u ^ 2 = 1` does not change the
sign of the product, so when `a + b` is odd the two signs multiply to the sign of `lc`.

## Main results

* `TauCeti.sign_mul_pow_mul_sign_mul_pow_of_sq_eq_one`: the product of the signs of `u * lc ^ a`
  and `u * lc ^ b` is the sign of `lc` when `u ^ 2 = 1` and `a + b` is odd.
-/

public section

namespace TauCeti

/-- If `u ^ 2 = 1` and `a + b` is odd, the signs of `u * lc ^ a` and `u * lc ^ b` multiply to the
sign of `lc`. -/
theorem sign_mul_pow_mul_sign_mul_pow_of_sq_eq_one {K : Type*} [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] {u : K} (hu : u ^ 2 = 1) (lc : K) {a b : ℕ} (hab : Odd (a + b)) :
    (SignType.sign (u * lc ^ a) : ℤ) * SignType.sign (u * lc ^ b) = SignType.sign lc := by
  have hprod : u * lc ^ a * (u * lc ^ b) = lc ^ (a + b) := by
    linear_combination (lc ^ a * lc ^ b) * hu
  rw [← SignType.coe_mul, ← sign_mul, hprod]
  simp [sign_pow, SignType.pow_odd _ hab]

end TauCeti
