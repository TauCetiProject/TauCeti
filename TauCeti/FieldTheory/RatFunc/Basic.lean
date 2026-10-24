/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Elementary nonvanishing in the rational function field

This file records that `X - a` and the radicands `c X ^ a (X - 1) ^ b` with `c ≠ 0` are nonzero
elements of `k(X)`, independently of the place theory of `k(X)`.

## Main results

* `RatFunc.X_sub_C_ne_zero`: `X - a` is nonzero in `k(X)`.
* `RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero`: `c X ^ a (X - 1) ^ b` is nonzero
  in `k(X)` for `c ≠ 0`.
-/

public section

namespace RatFunc

variable {k : Type*} [Field k]

/-- `X - a` is a nonzero element of `k(X)`. -/
theorem X_sub_C_ne_zero (a : k) : (X - C a : RatFunc k) ≠ 0 := by
  rw [← algebraMap_X, ← algebraMap_C, ← map_sub, Ne,
    map_eq_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))]
  exact Polynomial.X_sub_C_ne_zero a

/-- `c X ^ a (X - 1) ^ b` is a nonzero element of `k(X)` for `c ≠ 0`. -/
theorem algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero {c : k} (hc : c ≠ 0)
    (a b : ℤ) : algebraMap k (RatFunc k) c * X ^ a * (X - 1) ^ b ≠ 0 :=
  mul_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hc) (zpow_ne_zero a X_ne_zero))
    (zpow_ne_zero b (by simpa using X_sub_C_ne_zero (1 : k)))

end RatFunc
