/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.IsIntegral
public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.KummerPolynomial

/-!
# The minimal polynomial of `i`

For a field `K` mapping to `ℂ`, the minimal polynomial of `Complex.I` over `K` is `X ^ 2 + 1`
whenever that polynomial is irreducible over `K`, that is, whenever `-1` is not a square in `K`.
This holds over every ordered field, such as `ℚ` or `ℝ`, where `X ^ 2 + 1` has no root. Mathlib
records only that `Complex.I` is integral (`Complex.isIntegral_I`).

## Main results

* `Polynomial.irreducible_X_sq_add_one`: `X ^ 2 + 1` is irreducible over an ordered field.
* `Complex.minpoly_I`: the minimal polynomial of `i` over `K` is `X ^ 2 + 1` when the latter is
  irreducible.
-/

public section

open Polynomial

/-- **`X ^ 2 + 1` is irreducible over an ordered field**: a square is never `-1`. -/
theorem Polynomial.irreducible_X_sq_add_one (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : Irreducible (X ^ 2 + 1 : K[X]) := by
  have h := X_pow_sub_C_irreducible_of_prime Nat.prime_two (a := (-1 : K))
    fun b hb ↦ by nlinarith [sq_nonneg b]
  simpa [sub_eq_add_neg] using h

/-- **The minimal polynomial of `i` is `X ^ 2 + 1`** over any field `K` mapping to `ℂ` over which
`X ^ 2 + 1` is irreducible; for instance over an ordered field, by
`Polynomial.irreducible_X_sq_add_one`. -/
theorem Complex.minpoly_I {K : Type*} [Field K] [Algebra K ℂ]
    (h : Irreducible (X ^ 2 + 1 : K[X])) : minpoly K Complex.I = X ^ 2 + 1 :=
  (minpoly.eq_of_irreducible_of_monic h (by simp) (monic_X_pow_add_C 1 two_ne_zero)).symm
