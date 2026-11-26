/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.CMType.Prod

/-!
# CM types on `ℚ(i) × ℚ(√-3)`

This file checks the product API of `TauCeti.CMType` on `ℚ(i) × ℚ(√-3)`, with `ℚ(i)` the fourth
cyclotomic field `CyclotomicField 4 ℚ` and `ℚ(√-3)` the third cyclotomic field
`CyclotomicField 3 ℚ` (`ζ₃ = (-1 + √-3) / 2`). Both are quadratic, so every CM type on the
product has `(2 + 2) / 2 = 2` elements (`natCard_eq_two`).
-/

public section

namespace TauCeti.CMTypeProdExample

/-- `ℚ(i)`, as the fourth cyclotomic field. -/
abbrev K₄ : Type := CyclotomicField 4 ℚ

/-- `ℚ(√-3)`, as the third cyclotomic field. -/
abbrev K₃ : Type := CyclotomicField 3 ℚ

local instance instIsCyclotomicExtensionK₄ : IsCyclotomicExtension {4} ℚ K₄ :=
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  CyclotomicField.isCyclotomicExtension 4 ℚ

local instance instIsCyclotomicExtensionK₃ : IsCyclotomicExtension {3} ℚ K₃ :=
  have : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
  CyclotomicField.isCyclotomicExtension 3 ℚ

/-- `ℚ(i)` is quadratic. -/
theorem finrank_K₄ : Module.finrank ℚ K₄ = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 4 K₄]
  decide

/-- `ℚ(√-3)` is quadratic. -/
theorem finrank_K₃ : Module.finrank ℚ K₃ = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K₃]
  decide

/-- **Every CM type on `ℚ(i) × ℚ(√-3)` has two elements.** -/
theorem natCard_eq_two (Φ : CMType (K₄ × K₃)) : Nat.card Φ = 2 := by
  have h := Φ.two_mul_natCard_eq_finrank_add_finrank
  rw [finrank_K₄, finrank_K₃] at h
  omega

end TauCeti.CMTypeProdExample
