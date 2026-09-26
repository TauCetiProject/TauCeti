/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Minimal polynomials of quadratic elements

This file collects reusable facts about minimal polynomials of quadratic elements.

## Main results

* `TauCeti.Algebra.minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two`: the minimal polynomial
  of a quadratic element of an `F`-algebra whose square is in the base field `F`.
* `IsIntegral.exists_quadratic_relation`: a degree-two integral element of a ring algebra
  satisfies a monic quadratic relation over its commutative base ring.
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

/-- An integral element of degree two satisfies a monic quadratic relation over the base ring. -/
theorem IsIntegral.exists_quadratic_relation {K L : Type*} [CommRing K] [Ring L]
    [Algebra K L] {y : L} (hyint : IsIntegral K y)
    (hdeg : (minpoly K y).natDegree = 2) :
    ∃ b c : K, y ^ 2 + algebraMap K L b * y + algebraMap K L c = 0 := by
  cases subsingleton_or_nontrivial K with
  | inl h => simp [Polynomial.natDegree_of_subsingleton] at hdeg
  | inr h =>
    obtain ⟨b, c, hpoly⟩ :=
      Polynomial.isMonicOfDegree_two_iff.mp ⟨hdeg, minpoly.monic hyint⟩
    refine ⟨b, c, ?_⟩
    have h0 := minpoly.aeval K y
    rw [hpoly] at h0
    simpa using h0
