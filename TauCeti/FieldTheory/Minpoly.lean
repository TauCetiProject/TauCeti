/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Minimal polynomials of quadratic elements

This file collects reusable facts about minimal polynomials of quadratic elements.

## Main results

* `TauCeti.Algebra.minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two`: the minimal polynomial
  of a quadratic element of an `F`-algebra whose square is in the base field `F`.
-/

public section

open Polynomial

namespace TauCeti.Algebra

/-- The minimal polynomial of a quadratic element whose square is `r` is `X² - r`.

Only the base `F` need be a field; `L` is an arbitrary `F`-algebra ring, so this also covers
quadratic elements of noncommutative algebras, such as `i` in a quaternion algebra. -/
theorem minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two {F L : Type*} [Field F] [Ring L]
    [Algebra F L] {x : L} {r : F}
    (hx2 : x ^ 2 = algebraMap F L r) (hdegree : (minpoly F x).natDegree = 2) :
    minpoly F x = X ^ 2 - C r := by
  have hxint : IsIntegral F x := minpoly.ne_zero_iff.mp fun hzero ↦ by
    simp [hzero] at hdegree
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hxint)
    (Polynomial.monic_X_pow_sub_C r (by norm_num)) (minpoly.dvd F x ?_) ?_
  · simp [hx2]
  · rw [hdegree, Polynomial.natDegree_X_pow_sub_C]

end TauCeti.Algebra
