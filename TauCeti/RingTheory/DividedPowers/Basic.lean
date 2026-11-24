/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Complements on divided powers

This file provides general infrastructure for Mathlib's `DividedPowers` structure.

## Main results

* `DividedPowers.dpow_eqRec`: transporting a `DividedPowers` structure along an equality of ideals
  preserves `dpow`.
-/

public section

namespace DividedPowers

/-- Transporting a `DividedPowers` structure along an equality of ideals preserves `dpow`. -/
@[simp]
theorem dpow_eqRec {A : Type*} [CommSemiring A] {I₁ I₂ : Ideal A} (e : I₁ = I₂)
    (h₁ : DividedPowers I₁) (n : ℕ) (z : A) :
    (e ▸ h₁).dpow n z = h₁.dpow n z := by
  cases e
  rfl

end DividedPowers
