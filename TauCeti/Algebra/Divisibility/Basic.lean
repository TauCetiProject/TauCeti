/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Regular.Basic

/-!
# Divisibility of left-regular elements

In a commutative semigroup, every divisor of a left-regular element is left-regular.
-/

public section

/-- Any divisor of a left-regular element in a commutative semigroup is left-regular. -/
theorem IsLeftRegular.of_dvd {M : Type*} [CommSemigroup M] {f g : M}
    (hf : IsLeftRegular f) (hg : g ∣ f) : IsLeftRegular g := by
  obtain ⟨c, rfl⟩ := hg
  rw [mul_comm] at hf
  exact hf.of_mul
