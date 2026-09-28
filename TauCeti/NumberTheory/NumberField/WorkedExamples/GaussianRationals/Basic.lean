/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.Basic
public import TauCeti.NumberTheory.NumberField.IntrinsicLabel
public import TauCeti.NumberTheory.NumberField.Monogenic
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# Invariants of `ℚ(i)`

Let `K` be a number field generated over `ℚ` by an algebraic integer `θ` with
`minpoly ℤ θ = X² + 1`, that is `K = ℚ(i)` presented by a square root of `−1`. The radicand
`−1` is `3` modulo `4`, so the quadratic-field theory of the radicand presentation applies
directly: `𝓞 K = ℤ[θ]`, the field is monogenic with index `1`, and `discr K = 4 · (−1) = −4`.
The negative discriminant forces one complex place in degree two, so the signature is `(0, 1)`
and the intrinsic label prefix is `2.0.4`.

## Main results

* `TauCeti.NumberField.GaussianRationals.sq_eq_neg_one`: `θ² = −1`.
* `TauCeti.NumberField.GaussianRationals.finrank_eq_two`: `[K : ℚ] = 2`.
* `TauCeti.NumberField.GaussianRationals.adjoin_eq_top`: `𝓞 K = ℤ[θ]`, with `index_eq_one` and
  `isMonogenic`.
* `TauCeti.NumberField.GaussianRationals.discr_eq_neg_four`: `discr K = −4`.
* `TauCeti.NumberField.GaussianRationals.isTotallyComplex`, `nrRealPlaces_eq_zero`,
  `nrComplexPlaces_eq_one`: the signature is `(0, 1)`; `hasLMFDBIntrinsicLabel`: the
  intrinsic label prefix is `2.0.4`.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField.GaussianRationals

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
/-- The defining identity `θ² = −1`. -/
theorem sq_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 + 1) : θ ^ 2 = -1 := by
  have h := minpoly.aeval ℤ θ
  simp only [hmin, map_add, map_pow, aeval_X, map_one] at h
  linear_combination h

omit [NumberField K] in
/-- The minimal polynomial `X² + 1` in the radicand form `X² − C (−1)` of the quadratic-field
theory. -/
theorem minpoly_eq_X_sq_sub_C (hmin : minpoly ℤ θ = X ^ 2 + 1) :
    minpoly ℤ θ = X ^ 2 - C (-1) := by
  rw [hmin, map_neg, map_one, sub_neg_eq_add]

/-- `ℚ(i)` has degree `2`. -/
theorem finrank_eq_two (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Module.finrank ℚ K = 2 :=
  finrank_rat_eq_two (minpoly_eq_X_sq_sub_C hmin) hgen

/-- **The ring of integers of `ℚ(i)` is `ℤ[θ]`**: the radicand `−1` is not `1` modulo `4`. -/
theorem adjoin_eq_top (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Algebra.adjoin ℤ {θ} = ⊤ :=
  adjoin_gen_eq_top_of_mod_four_ne_one (minpoly_eq_X_sq_sub_C hmin) hgen
    isUnit_one.neg.squarefree (by decide)

/-- The generator `θ` has index `1` in the full ring of integers. -/
theorem index_eq_one (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    IntegralPrimitiveElement.index (⟨θ, hgen⟩ : IntegralPrimitiveElement K) = 1 := by
  have h : IntegralPrimitiveElement.adjoin (⟨θ, hgen⟩ : IntegralPrimitiveElement K) = ⊤ :=
    (IntegralPrimitiveElement.adjoin_def _).trans (adjoin_eq_top hmin hgen)
  exact (IntegralPrimitiveElement.index_eq_one_iff _).mpr h

/-- `ℚ(i)` is monogenic, generated integrally by `θ`. -/
theorem isMonogenic (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsMonogenic K :=
  isMonogenic_def.mpr ⟨θ, adjoin_eq_top hmin hgen⟩

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

/-- `ℚ(i)` has no real place: its signature is `(0, 1)`. -/
theorem nrRealPlaces_eq_zero (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : nrRealPlaces K = 0 := by
  have h := card_add_two_mul_card_eq_rank K
  rw [finrank_eq_two hmin hgen, nrComplexPlaces_eq_one hmin hgen] at h
  omega

/-- `ℚ(i)` is totally complex. -/
theorem isTotallyComplex (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsTotallyComplex K :=
  nrRealPlaces_eq_zero_iff.mp (nrRealPlaces_eq_zero hmin hgen)

/-- The intrinsic label prefix of `ℚ(i)` is `2.0.4`. -/
theorem hasLMFDBIntrinsicLabel (hmin : minpoly ℤ θ = X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : HasLMFDBIntrinsicLabel K 2 0 4 := by
  rw [hasLMFDBIntrinsicLabel_iff]
  refine ⟨finrank_eq_two hmin hgen, nrRealPlaces_eq_zero hmin hgen, ?_⟩
  rw [discr_eq_neg_four hmin hgen]
  norm_num

end TauCeti.NumberField.GaussianRationals
