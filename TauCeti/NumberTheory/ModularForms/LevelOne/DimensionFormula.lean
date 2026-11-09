/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Odd-weight vanishing for level-one cusp forms

Mathlib's `Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula` proves that every level-one
modular form of odd weight vanishes (`ModularForm.levelOne_odd_weight_eq_zero`). This file records
the `CuspForm` companion via the injective inclusion `CuspForm.toModularFormₗ`.

## Main results

* `CuspForm.levelOne_odd_weight_eq_zero`: every cusp form of odd weight on `SL(2, ℤ)` is zero.
-/

public section

open scoped MatrixGroups

namespace CuspForm

/-- A level-one cusp form of odd weight is zero, the `CuspForm` companion to
`ModularForm.levelOne_odd_weight_eq_zero`. -/
theorem levelOne_odd_weight_eq_zero {k : ℤ} (hk : Odd k) (f : CuspForm 𝒮ℒ k) : f = 0 :=
  toModularFormₗ_injective (ModularForm.levelOne_odd_weight_eq_zero hk f)

end CuspForm
