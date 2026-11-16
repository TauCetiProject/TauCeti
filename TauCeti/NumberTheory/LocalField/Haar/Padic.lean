/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Haar.Basic
public import TauCeti.NumberTheory.LocalField.Padic

/-!
# Distributive Haar character on `ℚ_[p]`

This module specializes the local Haar character formula of
`TauCeti.NumberTheory.LocalField.Haar.Basic` to the `p`-adic numbers `ℚ_[p]`, identifying
`MeasureTheory.distribHaarChar ℚ_[p] a` with the `p`-adic norm `‖a‖₊`.

## Main results

* `Padic.distribHaarChar_eq_nnnorm`: `distribHaarChar ℚ_[p] a = ‖(a : ℚ_[p])‖₊`.
-/

public section

open MeasureTheory

namespace Padic

/-- On `ℚ_[p]`, the distributive Haar character of a unit `a ∈ ℚ_[p]ˣ` coincides with its `p`-adic
norm `‖a‖₊`. -/
@[simp, grind =]
theorem distribHaarChar_eq_nnnorm {p : ℕ} [Fact p.Prime] (a : ℚ_[p]ˣ) :
    distribHaarChar ℚ_[p] a = ‖(a : ℚ_[p])‖₊ := by
  rw [TauCeti.distribHaarChar_eq_normalizedAbsoluteValue, normalizedAbsoluteValue_eq_nnnorm]

end Padic
