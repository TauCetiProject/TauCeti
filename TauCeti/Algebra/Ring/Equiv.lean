/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv

/-!
# Binary quadratic equations under ring equivalences

A ring isomorphism `e : R ≃+* S` transports solutions of the binary quadratic equation
`a = x² - d y²` between `R` and `S` (`RingEquiv.exists_sq_sub_mul_sq_iff`), requiring no
commutativity, domain, or quadratic-extension structure.
-/

public section

namespace RingEquiv

/-- A ring isomorphism preserves solvability of the binary quadratic equation `a = x² - d y²`. -/
theorem exists_sq_sub_mul_sq_iff {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) (a d : R) :
    (∃ x y : S, e a = x ^ 2 - e d * y ^ 2) ↔ ∃ x y : R, a = x ^ 2 - d * y ^ 2 := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨e.symm x, e.symm y, e.injective (by simpa using h)⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨e x, e y, by simp⟩

end RingEquiv
