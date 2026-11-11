/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Minimal polynomials of pure elements, quadratic elements and non-zero-divisors

This file collects reusable facts about minimal polynomials of elements with a power in the base
field, of quadratic elements, and of non-zero-divisors.

## Main results

* `TauCeti.Algebra.minpoly_eq_X_pow_sub_C_of_pow_eq_of_natDegree_eq`: the minimal polynomial
  of an element `x` of an `F`-algebra with `x ^ n = r ∈ F` and minimal polynomial of degree `n`
  is `X ^ n - r`.
* `TauCeti.Algebra.exists_quadratic_relation_of_natDegree_minpoly_eq_two`: an element whose
  minimal polynomial has degree two satisfies a monic quadratic relation over the commutative
  base ring.
* `minpoly.coeff_zero_ne_zero_of_mem_nonZeroDivisors`: the minimal polynomial of an integral
  non-zero-divisor, in particular of an integral unit, has nonzero constant coefficient.
-/

public section

open Polynomial nonZeroDivisors

namespace TauCeti.Algebra

/-- If `x ^ n = r` for some `r` in the base field and the minimal polynomial of `x` has degree
`n ≠ 0`, then this minimal polynomial is `X ^ n - r`.

Only the base `F` need be a field; `L` is an arbitrary `F`-algebra ring, so this also covers
elements of noncommutative algebras, such as `i` in a quaternion algebra. -/
theorem minpoly_eq_X_pow_sub_C_of_pow_eq_of_natDegree_eq {F L : Type*} [Field F] [Ring L]
    [Algebra F L] {x : L} {n : ℕ} {r : F} (hn : n ≠ 0)
    (hxn : x ^ n = algebraMap F L r) (hdegree : (minpoly F x).natDegree = n) :
    minpoly F x = X ^ n - C r := by
  have hxint : IsIntegral F x :=
    minpoly.ne_zero_iff.mp fun hzero ↦ hn <| by simpa [hzero, eq_comm] using hdegree
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxint) (monic_X_pow_sub_C r hn)
    (minpoly.dvd F x (by simp [hxn])) ?_).symm
  rw [hdegree, natDegree_X_pow_sub_C]

/-- An element whose minimal polynomial has degree two satisfies a monic quadratic relation over
the base ring. -/
theorem exists_quadratic_relation_of_natDegree_minpoly_eq_two {K L : Type*} [CommRing K] [Ring L]
    [Algebra K L] {y : L} (hdeg : (minpoly K y).natDegree = 2) :
    ∃ b c : K, y ^ 2 + algebraMap K L b * y + algebraMap K L c = 0 := by
  cases subsingleton_or_nontrivial K
  · simp [natDegree_of_subsingleton] at hdeg
  have hyint : IsIntegral K y := by
    by_contra h
    simp [minpoly.eq_zero h] at hdeg
  obtain ⟨b, c, hpoly⟩ := isMonicOfDegree_two_iff.mp ⟨hdeg, minpoly.monic hyint⟩
  refine ⟨b, c, ?_⟩
  simpa [hpoly] using minpoly.aeval K y

end TauCeti.Algebra

/-- The minimal polynomial of an integral non-zero-divisor over a nontrivial commutative ring has
nonzero constant coefficient. Unlike `minpoly.coeff_zero_ne_zero`, neither the base ring nor the
algebra need be a domain; integral units are the main example. -/
theorem minpoly.coeff_zero_ne_zero_of_mem_nonZeroDivisors {A B : Type*} [CommRing A]
    [Nontrivial A] [Ring B] [Algebra A B] {x : B} (hx : IsIntegral A x) (hx₀ : x ∈ B⁰) :
    (minpoly A x).coeff 0 ≠ 0 := by
  intro h0
  have hm := minpoly.monic hx
  have h : divX (minpoly A x) * X = minpoly A x := by
    simpa [h0] using divX_mul_X_add (minpoly A x)
  have hq : (divX (minpoly A x)).Monic := monic_X.of_mul_monic_right (by rwa [h])
  have hX : Polynomial.aeval x (divX (minpoly A x)) = 0 :=
    (mem_nonZeroDivisors_iff.mp hx₀).2 _ <| by
      have hmx := minpoly.aeval A x
      rwa [← h, map_mul, aeval_X] at hmx
  exact (degree_divX_lt hm.ne_zero).not_ge (minpoly.min A x hq hX)
