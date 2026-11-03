/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Coefficients of symmetric polynomials in two variables

A polynomial `f(X, Y)` is symmetric when it is fixed by every permutation of its variables
(`MvPolynomial.IsSymmetric`). For two variables this says `f(X, Y) = f(Y, X)`, which this file
records coefficientwise.

## Main results

* `MvPolynomial.IsSymmetric.coeff_single_add_single`: the coefficients of a symmetric
  two-variable polynomial are symmetric.
-/

public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- The coefficients of a symmetric two-variable polynomial are symmetric: the coefficient of
`XⁱYʲ` equals that of `XʲYⁱ`. -/
theorem IsSymmetric.coeff_single_add_single {f : MvPolynomial (Fin 2) R}
    (hs : f.IsSymmetric) (i j : ℕ) :
    f.coeff (Finsupp.single 0 i + Finsupp.single 1 j) =
      f.coeff (Finsupp.single 0 j + Finsupp.single 1 i) := by
  have h := coeff_rename_mapDomain (Equiv.swap (0 : Fin 2) 1) (Equiv.injective _) f
    (Finsupp.single 0 j + Finsupp.single 1 i)
  rwa [hs (Equiv.swap 0 1), Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm] at h

end MvPolynomial
