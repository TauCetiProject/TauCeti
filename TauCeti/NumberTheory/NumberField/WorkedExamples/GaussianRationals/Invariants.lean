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
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# Invariants of `ℚ(i)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² + 1`: the radicand
`−1` is `3` modulo `4`, so the quadratic-field theory of the radicand presentation applies
directly: `𝓞 K = ℤ[θ]`, the field is monogenic with index `1`, and `discr K = 4 · (−1) = −4`.
The negative radicand rules out real places, so the signature is `(0, 1)` and the intrinsic
label prefix is `2.0.4`. Minkowski's bound `(4/π)^{r₂} · n!/nⁿ · √|discr K|` is `2√4/π < 2`,
so every ideal class contains an integral ideal of norm `1`: `𝓞 K` is a principal ideal domain
and the class number is `1`.

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

open Polynomial NumberField NumberField.InfinitePlace Nat Real
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


/-- **`ℤ[i]` is a principal ideal domain**: Minkowski's bound `(4/π) · (2!/2²) · √4 = 4/π` is
less than `2`, so every ideal class contains an integral ideal of norm `1`. -/
theorem isPrincipalIdealRing (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_eq_neg_four hmin hgen, finrank_eq_two hmin hgen, nrComplexPlaces_eq_one hmin hgen]
  simp only [Int.reduceNeg, abs_neg, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (by norm_num : (0 : ℝ) < 4), pow_one, Nat.cast_ofNat, factorial_two]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

/-- The class number of `ℚ(i)` is `1`. -/
theorem classNumber_eq_one (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : classNumber K = 1 :=
  classNumber_eq_one_iff.mpr (isPrincipalIdealRing hmin hgen)

end TauCeti.NumberField.GaussianRationals
