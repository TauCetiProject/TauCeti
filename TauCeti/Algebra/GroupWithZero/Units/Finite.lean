/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.OrderOfElement

/-!
# Powers in a finite group with zero

In a finite group with zero `G₀`, for instance a finite field, every element is fixed by the
`Nat.card G₀`-th power map. The nonzero elements are the units, one fewer than the elements
(`Nat.card_eq_card_units_add_one`), and by Lagrange's theorem (`pow_card_eq_one'`) each unit
`u` has `u ^ Nat.card G₀ˣ = 1`; multiplying once more by `u` gives `u ^ Nat.card G₀ = u`.

Mathlib states this for finite fields as `FiniteField.pow_card`, with the order written as
`Fintype.card`. The form here, with `Nat.card` and only `[Finite G₀]`, is the one in which an
equation such as `Nat.card K = q ^ 2` is rewritten.

## Main results

* `TauCeti.pow_natCard`: in a finite group with zero, `a ^ Nat.card G₀ = a`.
-/

public section

namespace TauCeti

/-- In a finite group with zero `G₀`, for instance a finite field, every element is fixed by the
`Nat.card G₀`-th power map. This is Mathlib's `FiniteField.pow_card` with the order written as
`Nat.card G₀` and only `[Finite G₀]` assumed; it is proved from Lagrange's theorem
`pow_card_eq_one'` on the units. -/
@[simp]
theorem pow_natCard {G₀ : Type*} [GroupWithZero G₀] [Finite G₀] (a : G₀) :
    a ^ Nat.card G₀ = a := by
  obtain rfl | ha := eq_or_ne a 0
  · exact zero_pow Nat.card_pos.ne'
  have h := congrArg Units.val (pow_card_eq_one' (x := Units.mk0 a ha))
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h
  rw [Nat.card_eq_card_units_add_one, pow_succ, h, one_mul]

end TauCeti
