/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Haar.Basic
public import TauCeti.RingTheory.LaurentSeries.LocalField

/-!
# Distributive Haar character on `F⸨X⸩`

This module specializes `TauCeti.NumberTheory.LocalField.Haar.Basic` to the formal Laurent series
field `F⸨X⸩` over a finite field `F`, covering the positive-characteristic case of nonarchimedean
local fields: the uniformizer `X` (`TauCeti.LaurentSeries.XUnit F`) has distributive Haar character
`(Nat.card F)⁻¹` and pushes every additive Haar measure forward to `(Nat.card F) • μ`.

## Main results

* `TauCeti.LaurentSeries.distribHaarChar_XUnit`: `distribHaarChar F⸨X⸩ (XUnit F) = (Nat.card F)⁻¹`.
* `TauCeti.LaurentSeries.map_XUnit_mul_left_addHaar`: left multiplication by `X` pushes every
  additive Haar measure `μ` on `F⸨X⸩` forward to `(Nat.card F) • μ`.
-/

public section

open MeasureTheory
open scoped LaurentSeries NNReal

namespace TauCeti.LaurentSeries

variable (F : Type*) [Field F] [Finite F]

/-- **Equal-characteristic uniformizer character.** Over a finite field `F` (covering the
positive-characteristic case of nonarchimedean local fields), the uniformizer `X` of `F⸨X⸩` has
distributive Haar character `(Nat.card F)⁻¹`. -/
@[simp, grind =]
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
