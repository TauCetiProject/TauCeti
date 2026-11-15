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
elements of `k(X)`, independently of the place theory of `k(X)`, and that a linear polynomial
`c X + d` in `k(X)` over an integral domain vanishes exactly when both coefficients do.

## Main results

* `TauCeti.RatFunc.X_sub_C_ne_zero`: `X - a` is nonzero in `k(X)`.
* `TauCeti.RatFunc.algebraMap_mul_X_zpow_mul_X_sub_one_zpow_ne_zero`: `c X ^ a (X - 1) ^ b` is
  nonzero in `k(X)` for `c ≠ 0`.
* `RatFunc.C_mul_X_add_C_ne_zero` and `RatFunc.C_mul_X_add_C_eq_zero_iff`: `c X + d` is nonzero in
  `K(X)` when `c` or `d` is, and it vanishes exactly when `c = d = 0`.
-/

public section

namespace TauCeti.RatFunc

open _root_.RatFunc

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

end TauCeti.RatFunc

namespace RatFunc

variable {K : Type*} [CommRing K] [IsDomain K]

/-- A nonzero linear polynomial in `X`, read in `k(X)`, is nonzero. -/
theorem C_mul_X_add_C_ne_zero {c d : K} (hcd : c ≠ 0 ∨ d ≠ 0) : C c * X + C d ≠ 0 := by
  have hmap : C c * X + C d =
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
    rw [map_add, map_mul, algebraMap_C, algebraMap_C, algebraMap_X]
  rw [hmap, Ne, map_eq_zero_iff _ (algebraMap_injective K)]
  intro h0
  have h1 : c = 0 := by simpa using congrArg (fun p : Polynomial K ↦ p.coeff 1) h0
  have h0' : d = 0 := by simpa using congrArg (fun p : Polynomial K ↦ p.coeff 0) h0
  rcases hcd with h | h
  · exact h h1
  · exact h h0'

/-- A linear polynomial in `X`, read in `k(X)`, vanishes exactly when both coefficients do. -/
theorem C_mul_X_add_C_eq_zero_iff {c d : K} : C c * X + C d = 0 ↔ c = 0 ∧ d = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hc, hd⟩ ↦ by simp [hc, hd]⟩
  by_contra hne
  exact C_mul_X_add_C_ne_zero (not_and_or.mp hne) h

end RatFunc
