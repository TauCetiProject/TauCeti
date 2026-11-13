/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.IsIntegral
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# The minimal polynomial of `i`

For an integrally closed domain `R` embedded in `ℂ`, the minimal polynomial of `Complex.I` over
`R` is `X ^ 2 + 1` whenever that polynomial is irreducible over `R`. This covers `ℤ` and every
field in which `-1` is not a square, in particular every ordered field, such as `ℚ` or `ℝ`, where
`X ^ 2 + 1` has no root (`Polynomial.irreducible_X_sq_add_one`). Mathlib records only that
`Complex.I` is integral (`Complex.isIntegral_I`).

## Main results

* `Complex.minpoly_I`: the minimal polynomial of `i` over `R` is `X ^ 2 + 1` when the latter is
  irreducible.
-/

public section

open Polynomial

/-- **The minimal polynomial of `i` is `X ^ 2 + 1`** over any integrally closed domain `R` embedded
in `ℂ` over which `X ^ 2 + 1` is irreducible; for instance over `ℤ`, or over an ordered field, by
`Polynomial.irreducible_X_sq_add_one`. -/
theorem Complex.minpoly_I {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra R ℂ] [Module.IsTorsionFree R ℂ] (h : Irreducible (X ^ 2 + 1 : R[X])) :
    minpoly R Complex.I = X ^ 2 + 1 :=
  have hI := Complex.isIntegral_I R
  eq_of_monic_of_associated (minpoly.monic hI) (monic_X_pow_add_C 1 two_ne_zero) <|
    (minpoly.prime_of_isIntegrallyClosed hI).irreducible.associated_of_dvd h <|
      minpoly.isIntegrallyClosed_dvd hI (by simp)
