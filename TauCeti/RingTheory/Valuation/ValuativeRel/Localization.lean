/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.RingTheory.Localization.Defs

/-!
# Valuative comparisons in a localization

Clear denominators in a valuative relation on a localization of a commutative semiring.
The localized denominators are units, so multiplication by them preserves comparisons
and nonvanishing. These facts also describe pullback on valuation spectra of rings.
-/

public section

namespace ValuativeRel

variable {A : Type*} [CommSemiring A] (S : Submonoid A) (B : Type*) [CommSemiring B]
  [Algebra A B] [IsLocalization S B] [ValuativeRel B]

/-- A comparison between two localization fractions is equivalent to the comparison obtained
by clearing their denominators. -/
lemma vle_mk'_iff (a₁ a₂ : A) (s₁ s₂ : S) :
    IsLocalization.mk' B a₁ s₁ ≤ᵥ IsLocalization.mk' B a₂ s₂ ↔
      algebraMap A B (a₁ * s₂) ≤ᵥ algebraMap A B (a₂ * s₁) := by
  have hs₁ : 0 <ᵥ algebraMap A B s₁ :=
    TauCeti.ValuativeRel.not_vle_zero_of_isUnit (IsLocalization.map_units B s₁)
  have hs₂ : 0 <ᵥ algebraMap A B s₂ :=
    TauCeti.ValuativeRel.not_vle_zero_of_isUnit (IsLocalization.map_units B s₂)
  rw [← mul_vle_mul_iff_left hs₁, ← mul_vle_mul_iff_left hs₂,
    mul_right_comm (IsLocalization.mk' B a₂ s₂)]
  simp only [IsLocalization.mk'_spec, ← map_mul]

/-- Multiplying a numerator by a localized denominator or placing it over any denominator
does not change whether its value is nonzero. -/
lemma not_vle_algebraMap_mul_den_zero_iff (a : A) (s t : S) :
    ¬ algebraMap A B (a * s) ≤ᵥ 0 ↔ ¬ IsLocalization.mk' B a t ≤ᵥ 0 := by
  have hs : 0 <ᵥ algebraMap A B s :=
    TauCeti.ValuativeRel.not_vle_zero_of_isUnit (IsLocalization.map_units B s)
  have hmap : algebraMap A B (a * s) ≤ᵥ 0 ↔ algebraMap A B a ≤ᵥ 0 := by
    simpa only [map_mul, zero_mul] using
      (mul_vle_mul_iff_left (x := algebraMap A B a) (y := 0) hs)
  have hmk := vle_mk'_iff S B a 0 t 1
  simp only [Submonoid.coe_one, mul_one, zero_mul, map_zero, IsLocalization.mk'_zero] at hmk
  exact not_congr (hmap.trans hmk.symm)

end ValuativeRel
