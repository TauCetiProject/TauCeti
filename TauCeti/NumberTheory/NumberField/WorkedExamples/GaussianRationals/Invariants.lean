/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.Basic
public import TauCeti.NumberTheory.NumberField.IntrinsicLabel
public import TauCeti.NumberTheory.NumberField.Monogenic
public import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.ClassNumber.SmallDiscriminant
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# Invariants of `ℚ(i)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² + 1`: the radicand
`−1` is `3` modulo `4`, so the quadratic-field theory of the radicand presentation applies
directly: `𝓞 K = ℤ[θ]`, the field is monogenic with index `1`, and `discr K = 4 · (−1) = −4`.
The negative radicand rules out real places, so the signature is `(0, 1)` and the intrinsic
label prefix is `2.0.4`. The discriminant is below the quadratic Minkowski threshold, so `𝓞 K` is
a principal ideal domain and the class number is `1`.

## Main results

* `TauCeti.NumberField.GaussianRationals.adjoin_eq_top`: `𝓞 K = ℤ[θ]`, with `index_eq_one` and
  `isMonogenic`.
* `TauCeti.NumberField.GaussianRationals.discr_eq_neg_four`: `discr K = −4`.
* `TauCeti.NumberField.GaussianRationals.isTotallyComplex`, `nrRealPlaces_eq_zero`,
  `nrComplexPlaces_eq_one`: the field is totally complex, of signature `(0, 1)`;
  `hasLMFDBIntrinsicLabel`: the intrinsic label prefix is `2.0.4`.
* `TauCeti.NumberField.GaussianRationals.isPrincipalIdealRing`, `classNumber_eq_one`: `𝓞 K` is a
  principal ideal domain, by Mathlib's Minkowski criterion.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField.GaussianRationals

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The ring of integers of `ℚ(i)` is `ℤ[θ]`**: the radicand `−1` is not `1` modulo `4`. -/
@[simp]
theorem adjoin_eq_top (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Algebra.adjoin ℤ {θ} = ⊤ :=
  adjoin_gen_eq_top_of_mod_four_ne_one (minpoly_eq_X_sq_sub_C hmin) hgen
    isUnit_one.neg.squarefree (by decide)

/-- The generator `θ` has index `1` in the full ring of integers. -/
@[simp]
theorem index_eq_one (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    IntegralPrimitiveElement.index (⟨θ, hgen⟩ : IntegralPrimitiveElement K) = 1 := by
  have h : IntegralPrimitiveElement.adjoin (⟨θ, hgen⟩ : IntegralPrimitiveElement K) = ⊤ :=
    (IntegralPrimitiveElement.adjoin_def _).trans (adjoin_eq_top hmin hgen)
  exact (IntegralPrimitiveElement.index_eq_one_iff _).mpr h

/-- `ℚ(i)` is monogenic, generated integrally by `θ`. -/
theorem isMonogenic (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsMonogenic K :=
  isMonogenic_of_mod_four_ne_one (minpoly_eq_X_sq_sub_C hmin) hgen isUnit_one.neg.squarefree
    (by decide)

/-- **The discriminant of `ℚ(i)` is `−4`.** -/
theorem discr_eq_neg_four (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : NumberField.discr K = -4 := by
  rw [discr_eq_four_mul_of_mod_four_ne_one (minpoly_eq_X_sq_sub_C hmin) hgen
    isUnit_one.neg.squarefree (by decide)]
  norm_num

/-- `ℚ(i)` has exactly one complex place: its discriminant `−4` is negative. -/
theorem nrComplexPlaces_eq_one (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : nrComplexPlaces K = 1 :=
  InfinitePlace.nrComplexPlaces_eq_one_of_discr_lt_zero
    (by rw [discr_eq_neg_four hmin hgen]; decide) (by rw [finrank_eq_two hmin hgen]; decide)

/-- A number field containing a square root of `−1` is totally complex. -/
theorem isTotallyComplex (hmin : minpoly ℤ θ = X ^ 2 + 1) : IsTotallyComplex K :=
  isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg (minpoly_eq_X_sq_sub_C hmin) (by norm_num)

/-- A number field containing a square root of `−1` has no real place. -/
theorem nrRealPlaces_eq_zero (hmin : minpoly ℤ θ = X ^ 2 + 1) : nrRealPlaces K = 0 :=
  nrRealPlaces_eq_zero_iff.mpr (isTotallyComplex hmin)

/-- The intrinsic label prefix of `ℚ(i)` is `2.0.4`. -/
theorem hasLMFDBIntrinsicLabel (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : HasLMFDBIntrinsicLabel K 2 0 4 := by
  rw [hasLMFDBIntrinsicLabel_iff]
  refine ⟨finrank_eq_two hmin hgen, nrRealPlaces_eq_zero hmin, ?_⟩
  rw [discr_eq_neg_four hmin hgen]
  norm_num


/-- **`ℤ[i]` is a principal ideal domain**: the discriminant `−4` is below the quadratic
Minkowski threshold `9` of `isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine`. -/
theorem isPrincipalIdealRing (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsPrincipalIdealRing (𝓞 K) :=
  isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine (finrank_eq_two hmin hgen)
    (by rw [discr_eq_neg_four hmin hgen]; norm_num)

/-- The class number of `ℚ(i)` is `1`. -/
theorem classNumber_eq_one (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : classNumber K = 1 :=
  classNumber_eq_one_iff.mpr (isPrincipalIdealRing hmin hgen)

end TauCeti.NumberField.GaussianRationals
