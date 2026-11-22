/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Haar.Basic
public import TauCeti.NumberTheory.LocalField.Padic

/-!
# Normalized additive Haar measure and character on `ℚ_[p]`

This module specializes the local Haar measure and character formulas of
`TauCeti.NumberTheory.LocalField.Haar.Basic` to the `p`-adic numbers `ℚ_[p]`, normalizing
`TauCeti.localAddHaar ℚ_[p]` on the `p`-adic integers `ℤ_[p]` and identifying
`MeasureTheory.distribHaarChar ℚ_[p] a` with the `p`-adic norm `‖a‖₊`.

## Main results

* `Padic.localAddHaar_padicIntSubring`, `Padic.localAddHaar_setOf_norm_le_one`,
  `Padic.localAddHaar_range_padicIntCoe`: `TauCeti.localAddHaar ℚ_[p]` assigns mass one to
  `PadicInt.subring p`, `{x : ℚ_[p] | ‖x‖ ≤ 1}`, and the image of `ℤ_[p]`.
* `Padic.distribHaarChar_eq_nnnorm`: `distribHaarChar ℚ_[p] a = ‖(a : ℚ_[p])‖₊`.
-/

public section

open MeasureTheory

namespace Padic

/-- The normalized additive Haar measure on `ℚ_[p]` gives `PadicInt.subring p` mass one. -/
@[simp, grind =]
theorem localAddHaar_padicIntSubring (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]]
    [BorelSpace ℚ_[p]] :
    TauCeti.localAddHaar ℚ_[p] (PadicInt.subring p : Set ℚ_[p]) = 1 := by
  rw [← integerRing_eq_subring p, TauCeti.localAddHaar_integer]

/-- The normalized additive Haar measure on `ℚ_[p]` gives the unit ball `{x : ℚ_[p] | ‖x‖ ≤ 1}`
mass one. -/
@[simp, grind =]
theorem localAddHaar_setOf_norm_le_one (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]]
    [BorelSpace ℚ_[p]] :
    TauCeti.localAddHaar ℚ_[p] {x : ℚ_[p] | ‖x‖ ≤ 1} = 1 := by
  have h : {x : ℚ_[p] | ‖x‖ ≤ 1} = (PadicInt.subring p : Set ℚ_[p]) := by
    ext x
    simp [PadicInt.mem_subring_iff]
  rw [h, localAddHaar_padicIntSubring]

/-- The normalized additive Haar measure on `ℚ_[p]` gives the image of `ℤ_[p]` mass one. -/
@[grind =]
theorem localAddHaar_range_padicIntCoe (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]]
    [BorelSpace ℚ_[p]] :
    TauCeti.localAddHaar ℚ_[p] (Set.range ((↑) : ℤ_[p] → ℚ_[p])) = 1 := by
  simp

/-- On `ℚ_[p]`, the distributive Haar character of a unit `a ∈ ℚ_[p]ˣ` coincides with its `p`-adic
norm `‖a‖₊`. -/
@[grind =]
theorem distribHaarChar_eq_nnnorm {p : ℕ} [Fact p.Prime] (a : ℚ_[p]ˣ) :
    distribHaarChar ℚ_[p] a = ‖(a : ℚ_[p])‖₊ := by
  rw [distribHaarChar_eq_normalizedAbsoluteValue a, normalizedAbsoluteValue_eq_nnnorm]

end Padic
