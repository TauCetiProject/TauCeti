/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Derivation

/-!
# Primitives of Hahn series with rational exponents

Over a `ℚ`-algebra `R`, termwise integration `t ^ q ↦ t ^ (q + 1) / (q + 1)` is an `R`-linear
operator `TauCeti.ratHahnSeriesPrimitive R` on `HahnSeries ℚ R`. The coefficient of `t ^ (-1)` has
no primitive, since `t ^ 0` has derivative zero; the operator discards it, and its value has
constant coefficient zero. Consequently it is a right inverse of the derivative
`TauCeti.ratHahnSeriesDerivation R` exactly on the residue-zero series, and the image of the
derivative is the set of series whose coefficient of `t ^ (-1)` vanishes. This is the
rational-exponent analogue of `TauCeti.laurentSeriesPrimitive`.

Integration shifts every exponent by one, so it does not change the denominators of exponents;
this is what lets it restrict to the Puiseux field.

## Main definitions

* `TauCeti.ratHahnSeriesPrimitive R`: termwise integration with constant coefficient zero.

## Main results

* `TauCeti.ratHahnSeriesDerivation_ratHahnSeriesPrimitive`: differentiating the primitive
  removes exactly the residue term.
* `TauCeti.ratHahnSeriesPrimitive_ratHahnSeriesDerivation`: integrating a derivative removes
  exactly the constant term.
* `TauCeti.mem_range_ratHahnSeriesDerivation_iff`: the derivatives are exactly the series with
  coefficient of `t ^ (-1)` zero.
* `TauCeti.ratHahnSeriesDerivation_eq_iff_eq_ratHahnSeriesPrimitive_add_single`: the primitives
  of a residue-zero series differ from the normalized one by a constant.
-/

public section

open HahnSeries

namespace TauCeti

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- **Termwise integration** of Hahn series with rational exponents: the coefficient of `t ^ q` is
`q⁻¹` times the coefficient of `t ^ (q - 1)`. For `q = 0` this is zero, so the residue term
`t ^ (-1)` is discarded and the constant coefficient of the result is zero. -/
noncomputable def ratHahnSeriesPrimitive : HahnSeries ℚ R →ₗ[R] HahnSeries ℚ R where
  toFun x :=
    { coeff q := q⁻¹ • x.coeff (q - 1)
      isPWO_support' := by
        refine (x.isPWO_support.image_of_monotone (add_left_mono (a := (1 : ℚ)))).mono
          fun q hq ↦ ⟨q - 1, right_ne_zero_of_smul hq, sub_add_cancel q 1⟩ }
  map_add' x y := by
    ext q
    simp
  map_smul' r x := by
    ext q
    simp

variable {R}

/-- The coefficient of `t ^ q` in the primitive of `x` is `q⁻¹` times the coefficient of
`t ^ (q - 1)` in `x`. -/
@[simp]
theorem coeff_ratHahnSeriesPrimitive (x : HahnSeries ℚ R) (q : ℚ) :
    (ratHahnSeriesPrimitive R x).coeff q = q⁻¹ • x.coeff (q - 1) :=
  (rfl)

/-- Integration shifts the support up by one. -/
theorem support_ratHahnSeriesPrimitive_subset (x : HahnSeries ℚ R) :
    (ratHahnSeriesPrimitive R x).support ⊆ (· + 1) '' x.support := fun q hq ↦
  ⟨q - 1, right_ne_zero_of_smul hq, sub_add_cancel q 1⟩

/-- Integration of a monomial: `r t ^ q` integrates to `(q + 1)⁻¹ r t ^ (q + 1)`, which is zero for
`q = -1`. -/
@[simp]
theorem ratHahnSeriesPrimitive_single (q : ℚ) (r : R) :
    ratHahnSeriesPrimitive R (single q r) = single (q + 1) ((q + 1)⁻¹ • r) := by
  ext p
  rw [coeff_ratHahnSeriesPrimitive]
  by_cases hp : p = q + 1
  · simp [hp]
  · rw [coeff_single_of_ne (by rintro rfl; simp at hp), coeff_single_of_ne hp, smul_zero]

/-- Differentiating the primitive removes exactly the residue term. -/
theorem ratHahnSeriesDerivation_ratHahnSeriesPrimitive (x : HahnSeries ℚ R) :
    ratHahnSeriesDerivation R (ratHahnSeriesPrimitive R x) = x - single (-1) (x.coeff (-1)) := by
  ext q
  rw [coeff_ratHahnSeriesDerivation, coeff_ratHahnSeriesPrimitive, add_sub_cancel_right, smul_smul,
    coeff_sub, coeff_single]
  by_cases hq : q = -1
  · simp [hq]
  · rw [mul_inv_cancel₀ (by rintro h; exact hq (eq_neg_of_add_eq_zero_left h)), one_smul]
    simp [hq]

/-- Integrating a derivative removes exactly the constant term. -/
theorem ratHahnSeriesPrimitive_ratHahnSeriesDerivation (x : HahnSeries ℚ R) :
    ratHahnSeriesPrimitive R (ratHahnSeriesDerivation R x) = x - single 0 (x.coeff 0) := by
  ext q
  rw [coeff_ratHahnSeriesPrimitive, coeff_ratHahnSeriesDerivation_sub_one, smul_smul, coeff_sub,
    coeff_single]
  by_cases hq : q = 0
  · simp [hq]
  · rw [inv_mul_cancel₀ hq, one_smul]
    simp [hq]

/-- A residue-zero series is the derivative of its primitive. -/
theorem ratHahnSeriesDerivation_ratHahnSeriesPrimitive_of_coeff_neg_one_eq_zero
    {x : HahnSeries ℚ R} (hx : x.coeff (-1) = 0) :
    ratHahnSeriesDerivation R (ratHahnSeriesPrimitive R x) = x := by
  rw [ratHahnSeriesDerivation_ratHahnSeriesPrimitive, hx, single_eq_zero, sub_zero]

/-- **Primitive criterion**: a Hahn series with rational exponents is a derivative exactly when its
coefficient of `t ^ (-1)` vanishes. -/
theorem mem_range_ratHahnSeriesDerivation_iff {x : HahnSeries ℚ R} :
    x ∈ Set.range (ratHahnSeriesDerivation R) ↔ x.coeff (-1) = 0 := by
  refine ⟨?_, fun hx ↦ ⟨_, ratHahnSeriesDerivation_ratHahnSeriesPrimitive_of_coeff_neg_one_eq_zero
    hx⟩⟩
  rintro ⟨y, rfl⟩
  rw [coeff_ratHahnSeriesDerivation, neg_add_cancel, zero_smul]

/-- The primitives of a residue-zero series are its normalized primitive plus a constant. -/
theorem ratHahnSeriesDerivation_eq_iff_eq_ratHahnSeriesPrimitive_add_single
    {x y : HahnSeries ℚ R} (hx : x.coeff (-1) = 0) :
    ratHahnSeriesDerivation R y = x ↔ ∃ c : R, y = ratHahnSeriesPrimitive R x + single 0 c := by
  refine ⟨fun h ↦ ⟨y.coeff 0, ?_⟩, ?_⟩
  · rw [← h, ratHahnSeriesPrimitive_ratHahnSeriesDerivation, sub_add_cancel]
  · rintro ⟨c, rfl⟩
    rw [map_add, ratHahnSeriesDerivation_ratHahnSeriesPrimitive_of_coeff_neg_one_eq_zero hx,
      ratHahnSeriesDerivation_single, zero_sub, zero_smul, single_eq_zero, add_zero]

end TauCeti
