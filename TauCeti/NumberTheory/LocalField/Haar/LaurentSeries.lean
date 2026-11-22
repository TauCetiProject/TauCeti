/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Haar.Basic
public import TauCeti.RingTheory.LaurentSeries.LocalField

/-!
# Normalized additive Haar measure and character on `F⸨X⸩`

This module specializes `TauCeti.NumberTheory.LocalField.Haar.Basic` to the formal Laurent series
field `F⸨X⸩` over a finite field `F`, covering the positive-characteristic case of nonarchimedean
local fields: `TauCeti.localAddHaar F⸨X⸩` assigns mass one to the power-series subring `F⟦X⟧`,
and the uniformizer `X` (`TauCeti.LaurentSeries.XUnit F`) has distributive Haar character
`(Nat.card F)⁻¹` and pushes every additive Haar measure forward to `(Nat.card F) • μ`.

## Main results

* `TauCeti.LaurentSeries.localAddHaar_range_ofPowerSeries`: `TauCeti.localAddHaar F⸨X⸩` gives the
  power-series subring `Set.range (HahnSeries.ofPowerSeries ℤ F)` mass one.
* `TauCeti.LaurentSeries.distribHaarChar_XUnit`: `distribHaarChar F⸨X⸩ (XUnit F) = (Nat.card F)⁻¹`.
* `TauCeti.LaurentSeries.map_XUnit_mul_left_addHaar`: left multiplication by `X` pushes every
  additive Haar measure `μ` on `F⸨X⸩` forward to `(Nat.card F) • μ`.
-/

public section

open MeasureTheory
open scoped LaurentSeries NNReal ValuativeRel

namespace TauCeti.LaurentSeries

variable (F : Type*) [Field F] [Finite F]

/-- The normalized additive Haar measure on `F⸨X⸩` gives the power-series subring
`Set.range (HahnSeries.ofPowerSeries ℤ F)` mass one. -/
@[simp, grind =]
theorem localAddHaar_range_ofPowerSeries [MeasurableSpace F⸨X⸩] [BorelSpace F⸨X⸩] :
    localAddHaar F⸨X⸩ (Set.range (HahnSeries.ofPowerSeries ℤ F)) = 1 := by
  have h : Set.range (HahnSeries.ofPowerSeries ℤ F) = (𝒪[F⸨X⸩] : Set F⸨X⸩) := by
    rw [integer_eq_powerSeries_as_subring F]
    simp [_root_.LaurentSeries.powerSeries_as_subring]
  rw [h, localAddHaar_integer]

/-- **Equal-characteristic uniformizer character.** Over a finite field `F` (covering the
positive-characteristic case of nonarchimedean local fields), the uniformizer `X` of `F⸨X⸩` has
distributive Haar character `(Nat.card F)⁻¹`. -/
@[grind =]
theorem distribHaarChar_XUnit :
    distribHaarChar F⸨X⸩ (XUnit F) = (Nat.card F : ℝ≥0)⁻¹ := by
  rw [distribHaarChar_of_isUniformizer (isUniformizer_XUnit F), natCard_residueField]

/-- In `F⸨X⸩` over a finite field `F`, left multiplication by `X` pushes every additive Haar measure
`μ` forward to `(Nat.card F) • μ`. -/
theorem map_XUnit_mul_left_addHaar [MeasurableSpace F⸨X⸩] [BorelSpace F⸨X⸩]
    (μ : Measure F⸨X⸩) [μ.IsAddHaarMeasure] :
    Measure.map (((XUnit F : F⸨X⸩ˣ) : F⸨X⸩) * ·) μ = (Nat.card F : ℝ≥0) • μ := by
  rw [Measure.map_mul_left_addHaar_of_isUniformizer μ (isUniformizer_XUnit F), natCard_residueField]

end TauCeti.LaurentSeries
