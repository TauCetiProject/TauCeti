/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.Multiquadratic.Three.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# The class number of `ℚ(√3)`

This file proves that the real quadratic field `ℚ(√3)` has class number `1`.

Since `3 ≡ 3 (mod 4)` the ring of integers is `ℤ[√3]` and the discriminant is `12`. The field is
totally real, so its Minkowski bound is `(2!/2²) · √12 = √3 < 2`: every ideal class has an
integral representative of norm `1`, that is, the unit ideal. Mathlib's
`NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` packages exactly this
comparison, and `12 < 16` is the required numerical inequality.

Total reality is what makes the bound small enough: at absolute discriminant `12`, the
hypothetical imaginary-signature Minkowski bound would carry the extra factor `4/π`, giving
`(4/π)·√12/2 ≈ 2.2`, which would not suffice.

The main theorem is stated for any number field with an integral generator of minimal polynomial
`X² - 3`; the final theorem applies it to the `AdjoinRoot (X² - 3)` model.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Chapter 5.

## Main results

* `TauCeti.NumberField.discr_eq_twelve_of_minpoly_eq_X_sq_sub_three`: every presentation of
  `ℚ(√3)` by an integral generator has discriminant `12`.
* `TauCeti.NumberField.discr_adjoinRoot_sqrt_three_eq_twelve`: the discriminant of the concrete
  `AdjoinRoot (X² - 3)` model is `12`.
* `TauCeti.NumberField.classNumber_eq_one_of_minpoly_eq_X_sq_sub_three`: every presentation of
  `ℚ(√3)` by an integral generator has class number one.
* `TauCeti.NumberField.classNumber_adjoinRoot_sqrt_three_eq_one`: the result for the concrete
  `AdjoinRoot (X² - 3)` model.
-/

public section

open Module NumberField Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- The discriminant of a presentation of `ℚ(√3)` is `12`. -/
theorem discr_eq_twelve_of_minpoly_eq_X_sq_sub_three
    (hmin : minpoly ℤ θ = X ^ 2 - C (3 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    NumberField.discr K = 12 := by
  simpa using NumberField.discr_eq_four_mul_of_mod_four_ne_one hmin hgen
    (Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree (by decide)

/-- **Worked example.** The concrete number field `AdjoinRoot (X² - 3)`, modelling `ℚ(√3)`, has
discriminant `12`. -/
@[simp]
theorem discr_adjoinRoot_sqrt_three_eq_twelve :
    NumberField.discr (AdjoinRoot (X ^ 2 - C (3 : ℚ))) = 12 := by
  obtain ⟨θ, hmin, hgen⟩ := exists_minpoly_eq_X_sq_sub_three_and_adjoin_eq_top
  exact discr_eq_twelve_of_minpoly_eq_X_sq_sub_three hmin hgen

/-- **The class number of `ℚ(√3)` is one.** This presentation-independent statement assumes an
integral generator with minimal polynomial `X² - 3` which generates the field over `ℚ`. -/
theorem classNumber_eq_one_of_minpoly_eq_X_sq_sub_three
    (hmin : minpoly ℤ θ = X ^ 2 - C (3 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : NumberField.classNumber K = 1 := by
  have hfin : finrank ℚ K = 2 := NumberField.finrank_rat_eq_two hmin hgen
  have _ : IsTotallyReal K :=
    NumberField.isTotallyReal_of_minpoly_eq_X_sq_sub_C_of_nonneg hmin hgen (by norm_num)
  have hcomplex : InfinitePlace.nrComplexPlaces K = 0 :=
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K
  have hdisc := discr_eq_twelve_of_minpoly_eq_X_sq_sub_three hmin hgen
  refine NumberField.classNumber_eq_one_iff.mpr ?_
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hdisc, hcomplex, hfin]
  norm_num [Nat.factorial]

/-- **Worked example.** The concrete number field `AdjoinRoot (X² - 3)`, modelling `ℚ(√3)`, has
class number `1`. -/
@[simp]
theorem classNumber_adjoinRoot_sqrt_three_eq_one :
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (3 : ℚ))) = 1 := by
  obtain ⟨θ, hmin, hgen⟩ := exists_minpoly_eq_X_sq_sub_three_and_adjoin_eq_top
  exact classNumber_eq_one_of_minpoly_eq_X_sq_sub_three hmin hgen

end TauCeti.NumberField
