/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import Mathlib.RingTheory.Valuation.ValuativeRel.Trivial
public import TauCeti.NumberTheory.LocalField.ModelField

/-!
# Tests for model fields

* `ℚ_[p]` is a model field, through the instance for nonarchimedean local fields, so its
  valuation ring `𝒪[ℚ_[p]]` is a discrete valuation ring.
* A field whose valuative relation is the trivial one (compatible with the trivial valuation `1`)
  is not a model field.
-/

public section

open ValuativeRel

namespace TauCeti.Examples.ModelField

/-- `ℚ_[p]` is a model field. -/
example (p : ℕ) [Fact p.Prime] : ModelField ℚ_[p] := inferInstance

/-- The valuation ring of `ℚ_[p]` is a discrete valuation ring, through `ModelField`. -/
example (p : ℕ) [Fact p.Prime] : IsDiscreteValuationRing 𝒪[ℚ_[p]] :=
  ModelField.isDiscreteValuationRing ℚ_[p]

/-- A trivially valued field is not a model field. -/
example (K Γ : Type*) [Field K] [DecidableEq K] [ValuativeRel K] [LinearOrderedCommGroupWithZero Γ]
    [Valuation.Compatible (1 : Valuation K Γ)] : ¬ ModelField K :=
  ModelField.not_of_not_isNontrivial K (not_isNontrivial_of_trivialRel (R := K) (Γ := Γ))

end TauCeti.Examples.ModelField
