/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.Norm

/-!
# The splitting of `5` in `ℚ(i)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² + 1`, the rational
prime `5 = (2 + θ)(2 − θ)` splits: the ideals `(2 + θ)` and `(2 − θ)` both have absolute norm
`5`, they are distinct, and they are the only ideals of `𝓞 K` of absolute norm `5`. So two
ideals of `ℚ(i)` share the norm `5`, the standard witness that regrouping ideal sums by norm is not
compatible with pointwise products.

The general quadratic splitting law `NumberField.ncard_primesOver_quadratic_iff` counts the primes
above `5` without naming them; here the two primes, and with them every ideal of norm `5`, are
given by explicit generators.

## Main results

* `TauCeti.NumberField.GaussianRationals.absNorm_span_two_add`,
  `absNorm_span_two_sub`: `N(2 + θ) = N(2 − θ) = 5`.
* `TauCeti.NumberField.GaussianRationals.span_two_add_ne_span_two_sub`: `(2 + θ) ≠ (2 − θ)`.
* `TauCeti.NumberField.GaussianRationals.absNorm_eq_five_iff`: the ideals of absolute norm `5`
  are exactly `(2 + θ)` and `(2 − θ)`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 1, §4,
  for the Gaussian integers and the splitting of primes `p ≡ 1 mod 4`.
-/

public section

open Polynomial NumberField Ideal
open scoped NumberField

namespace TauCeti.NumberField.GaussianRationals

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
/-- `5 = (2 + θ)(2 − θ)` in `𝓞 K`, since `θ² = −1`. -/
theorem two_add_mul_two_sub_eq_five (hmin : minpoly ℤ θ = X ^ 2 + 1) :
    (2 + θ) * (2 - θ) = 5 := by
  linear_combination -(sq_eq_neg_one hmin)

/-- The ideal `(2 + θ)` has absolute norm `5`: `N(2 + θ) = 2² − (−1) · 1²`. -/
theorem absNorm_span_two_add (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : absNorm (span {2 + θ}) = 5 := by
  have h := norm_int_add_mul_gen (minpoly_eq_X_sq_sub_C hmin) hgen 1 2
  norm_num at h
  rw [absNorm_span_singleton, h]
  rfl

/-- The ideal `(2 − θ)` has absolute norm `5`: `N(2 − θ) = 2² − (−1) · (−1)²`. -/
theorem absNorm_span_two_sub (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : absNorm (span {2 - θ}) = 5 := by
  have h := norm_int_add_mul_gen (minpoly_eq_X_sq_sub_C hmin) hgen (-1) 2
  norm_num [← sub_eq_add_neg] at h
  rw [absNorm_span_singleton, h]
  rfl

/-- **`(2 + θ)` and `(2 − θ)` are distinct ideals** in any number field containing `θ`. -/
theorem span_two_add_ne_span_two_sub (hmin : minpoly ℤ θ = X ^ 2 + 1) :
    span {2 + θ} ≠ span {2 - θ} := by
  intro h
  have hadd : 2 + θ ∈ span {2 + θ} := mem_span_singleton_self _
  have hsub : 2 - θ ∈ span {2 + θ} := h ▸ mem_span_singleton_self _
  have h5 : (5 : 𝓞 K) ∈ span {2 + θ} := two_add_mul_two_sub_eq_five hmin ▸ mul_mem_right _ _ hadd
  have hone : (1 : 𝓞 K) ∈ span {2 + θ} := by
    have h := sub_mem h5 (add_mem hadd hsub)
    convert h using 1; ring
  have hunit_add : IsUnit (2 + θ) := (span_singleton_eq_top.mp ((eq_top_iff_one _).mpr hone))
  have hunit_sub : IsUnit (2 - θ) := by
    apply span_singleton_eq_top.mp
    rw [← h]
    exact (eq_top_iff_one _).mpr hone
  have hunit_five : IsUnit (5 : 𝓞 K) := by
    rw [← two_add_mul_two_sub_eq_five hmin]
    exact hunit_add.mul hunit_sub
  have hnorm : IsUnit (Algebra.norm ℤ (S := 𝓞 K) (5 : 𝓞 K)) :=
    hunit_five.map (Algebra.norm ℤ)
  have hnormeq : Algebra.norm ℤ (S := 𝓞 K) (5 : 𝓞 K) =
      (5 : ℤ) ^ Module.finrank ℤ (𝓞 K) := Algebra.norm_natCast ℤ 5
  rw [hnormeq, isUnit_pow_iff (ne_of_gt (Module.finrank_pos :
    0 < Module.finrank ℤ (𝓞 K)))] at hnorm
  rcases Int.isUnit_iff.mp hnorm with h | h <;> omega

/-- **The ideals of `ℚ(i)` of absolute norm `5` are exactly `(2 + θ)` and `(2 − θ)`.**
This identifies the two terms in the norm-`5` fibre used to compute the zeta coefficient. -/
theorem absNorm_eq_five_iff (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {I : Ideal (𝓞 K)} :
    absNorm I = 5 ↔ I = span {2 + θ} ∨ I = span {2 - θ} := by
  have hirr : Irreducible (5 : ℕ) := (Nat.irreducible_iff_nat_prime 5).mpr Nat.prime_five
  -- An ideal of norm `5` containing `a` is the ideal `(a)`, when `(a)` also has norm `5`.
  have key (a : 𝓞 K) (ha : absNorm (span {a}) = 5) (hI : absNorm I = 5) (haI : a ∈ I) :
      I = span {a} := by
    have hprime : (span {a}).IsPrime := isPrime_of_irreducible_absNorm (ha ▸ hirr)
    have hbot : span {a} ≠ ⊥ := fun h ↦ by simp [h] at ha
    refine ((hprime.isMaximal hbot).eq_of_le (fun htop ↦ ?_)
      ((span_singleton_le_iff_mem I).mpr haI)).symm
    rw [htop, absNorm_top] at hI
    exact absurd hI (by norm_num)
  constructor
  · intro hI
    have hprime : I.IsPrime := isPrime_of_irreducible_absNorm (hI ▸ hirr)
    have h5 : (2 + θ) * (2 - θ) ∈ I := by
      rw [two_add_mul_two_sub_eq_five hmin]
      exact_mod_cast hI ▸ absNorm_mem I
    rcases hprime.mem_or_mem h5 with h | h
    · exact .inl (key _ (absNorm_span_two_add hmin hgen) hI h)
    · exact .inr (key _ (absNorm_span_two_sub hmin hgen) hI h)
  · rintro (rfl | rfl)
    · exact absNorm_span_two_add hmin hgen
    · exact absNorm_span_two_sub hmin hgen

end TauCeti.NumberField.GaussianRationals
