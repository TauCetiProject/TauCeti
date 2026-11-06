/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Minimal polynomials of quadratic elements and units

This file collects reusable facts about minimal polynomials of quadratic elements and of units.

## Main results

* `TauCeti.Algebra.minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two`: the minimal polynomial
  of a quadratic element of an `F`-algebra whose square is in the base field `F`.
* `IsIntegral.exists_quadratic_relation`: a degree-two integral element of a ring algebra
  satisfies a monic quadratic relation over its commutative base ring.
* `minpoly.coeff_zero_ne_zero_of_isUnit`: the minimal polynomial of an integral unit has nonzero
  constant coefficient.
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

/-- The minimal polynomial of an integral unit has nonzero constant coefficient. Unlike
`minpoly.coeff_zero_ne_zero`, the algebra need not be a domain. -/
theorem minpoly.coeff_zero_ne_zero_of_isUnit {A B : Type*} [Field A] [Ring B] [Algebra A B]
    {x : B} (hx : IsIntegral A x) (hu : IsUnit x) : (minpoly A x).coeff 0 ≠ 0 := by
  intro h0
  have hm : minpoly A x ≠ 0 := minpoly.ne_zero hx
  have hdiv : divX (minpoly A x) ≠ 0 := fun h ↦ hm (by rwa [divX_eq_zero_iff, h0, C_0] at h)
  have hX : Polynomial.aeval x (divX (minpoly A x)) = 0 := by
    have hmx := minpoly.aeval A x
    have h := divX_mul_X_add (minpoly A x)
    rw [h0, C_0, add_zero] at h
    rw [← h, map_mul, aeval_X] at hmx
    exact hu.mul_left_eq_zero.mp hmx
  exact absurd (minpoly.degree_le_of_ne_zero A x hdiv hX) (not_le.mpr (degree_divX_lt hm))
