/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Two algebraic elements lie in a common number field

Two elements of a field of characteristic zero that are algebraic over `ℚ` generate a finite
extension `ℚ⟮x, y⟯` of `ℚ`, which is a number field. This reduces statements about pairs of
algebraic numbers in an arbitrary characteristic-zero field to the number-field API.

## Main results

* `TauCeti.exists_numberField_mem`: two algebraic elements of `F` lie in a common intermediate
  number field.
-/

public section

open IntermediateField

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F]

/-- Two algebraic elements of `F` lie in a common intermediate number field. -/
theorem exists_numberField_mem {x y : F} (hx : IsAlgebraic ℚ x) (hy : IsAlgebraic ℚ y) :
    ∃ (K : IntermediateField ℚ F) (_ : NumberField K) (a b : K), (a : F) = x ∧ (b : F) = y := by
  have := finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  exact ⟨ℚ⟮x, y⟯, {}, ⟨x, mem_adjoin_pair_left ℚ x y⟩, ⟨y, mem_adjoin_pair_right ℚ x y⟩, rfl, rfl⟩

end TauCeti
