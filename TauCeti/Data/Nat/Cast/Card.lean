/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finiteness from a nonzero cast of cardinality

Since `Nat.card` vanishes on infinite types, a nonzero cast of the cardinality implies finiteness.
-/

public section

namespace TauCeti

/-- A type is finite if its cardinality has a nonzero cast. -/
theorem finite_of_natCast_card_ne_zero {α R : Type*} [AddMonoidWithOne R]
    (h : (Nat.card α : R) ≠ 0) : Finite α :=
  Nat.finite_of_card_ne_zero fun hcard ↦ h (by simp [hcard])

end TauCeti
