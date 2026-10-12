/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.Basic
public import TauCeti.NumberTheory.NumberField.Index.DedekindCubic.RingOfIntegers
public import TauCeti.NumberTheory.NumberField.IntrinsicLabel
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.NumberTheory.NumberField.Index.Discriminant

/-!
# Invariants of Dedekind's cubic field

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X³ − X² − 2X − 8`,
the ring of integers has the integral basis `(1, θ, (θ² − θ)/2)` of discriminant `−503`. This
file records the consequences: the field discriminant is `−503`, the generator `θ` has index
`2` in the ring of integers (since `disc(minpoly θ) = −2012 = 2² · (−503)`), the signature is
`(1, 1)` and the intrinsic label prefix is `3.1.503`. The integral basis is the one of
`TauCeti.NumberTheory.NumberField.Index.DedekindCubic.RingOfIntegers`.

## Main results

* `TauCeti.NumberField.dedekindCubic_discr_polynomial`: `disc(X³ − X² − 2X − 8) = −2012`.
* `TauCeti.NumberField.dedekindCubic_discr_eq_neg_five_hundred_three`: `discr K = −503`.
* `TauCeti.NumberField.dedekindCubic_index_eq_two`: `θ` has index `2`.
* `TauCeti.NumberField.dedekindCubic_nrComplexPlaces_eq_one`, `dedekindCubic_nrRealPlaces_eq_one`:
  the signature is `(1, 1)`; `dedekindCubic_hasLMFDBIntrinsicLabel`: the intrinsic label prefix
  is `3.1.503`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2, Exercise 1.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

-- Not a `simp` lemma: `simp` rewrites the constants `C 2` and `C 8` of the left-hand side to
-- numerals, so `simpNF` rejects the tag; the statement keeps the form of the minimal polynomial
-- used throughout the Dedekind-cubic files.
/-- The discriminant of Dedekind's cubic is `−2012 = 2² · (−503)`. -/
theorem dedekindCubic_discr_polynomial :
    (X ^ 3 - X ^ 2 - C 2 * X - C 8 : ℤ[X]).discr = -2012 := by
  rw [Polynomial.discr_of_degree_eq_three (by compute_degree <;> norm_num)]
  norm_num [coeff_add, coeff_sub, coeff_X_pow, coeff_one, coeff_C_mul, coeff_X, coeff_C]

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
  (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
  (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)

include hmin hgen

/-- **The discriminant of Dedekind's cubic field is `−503`**: the integral basis
`(1, θ, (θ² − θ)/2)` has discriminant `−503` and index `1`. -/
theorem dedekindCubic_discr_eq_neg_five_hundred_three : discr K = -503 := by
  have h := index_dedekindOrder_sq_mul_discr hmin hgen
  rw [dedekindOrderIndex_eq_one hmin hgen] at h
  simpa using h.symm

/-- **The generator `θ` has index `2`** in the ring of integers:
`disc(minpoly θ) = −2012 = index² · (−503)`. -/
theorem dedekindCubic_index_eq_two :
    IntegralPrimitiveElement.index (⟨θ, hgen⟩ : IntegralPrimitiveElement K) = 2 := by
  let t : IntegralPrimitiveElement K := ⟨θ, hgen⟩
  have hd := t.discr_minpoly_eq_index_sq_mul_discr
  simp only [t] at hd
  rw [hmin, dedekindCubic_discr_polynomial,
    dedekindCubic_discr_eq_neg_five_hundred_three hmin hgen] at hd
  have h4 : t.index ^ 2 = 2 ^ 2 := by
    have : (t.index : ℤ) ^ 2 = 2 ^ 2 := by linarith
    exact_mod_cast this
  exact Nat.pow_left_injective (by norm_num) h4

/-- There is exactly one complex infinite place: the discriminant `−503` is negative. -/
theorem dedekindCubic_nrComplexPlaces_eq_one : nrComplexPlaces K = 1 :=
  InfinitePlace.nrComplexPlaces_eq_one_of_discr_lt_zero
    (by rw [dedekindCubic_discr_eq_neg_five_hundred_three hmin hgen]; decide)
    (by rw [dedekindCubic_finrank_eq_three hmin hgen]; decide)

/-- There is exactly one real infinite place. -/
theorem dedekindCubic_nrRealPlaces_eq_one : nrRealPlaces K = 1 := by
  have h := card_add_two_mul_card_eq_rank K
  rw [dedekindCubic_finrank_eq_three hmin hgen, dedekindCubic_nrComplexPlaces_eq_one hmin hgen] at h
  omega

/-- The intrinsic label prefix is `3.1.503`. -/
theorem dedekindCubic_hasLMFDBIntrinsicLabel : HasLMFDBIntrinsicLabel K 3 1 503 := by
  rw [hasLMFDBIntrinsicLabel_iff]
  refine ⟨dedekindCubic_finrank_eq_three hmin hgen, dedekindCubic_nrRealPlaces_eq_one hmin hgen, ?_⟩
  rw [dedekindCubic_discr_eq_neg_five_hundred_three hmin hgen]
  norm_num

end TauCeti.NumberField
