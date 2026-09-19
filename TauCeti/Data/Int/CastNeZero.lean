/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Integer casts that stay nonzero

An even integer with nonzero cast keeps `2` nonzero: if `2` cast to the ring were zero then so
would be the cast of anything `2` divides.

Nonvanishing of the cast is all that is claimed. In a general ring that is weaker than the cast
being a unit, and it is the form a hypothesis like `(n : R) ≠ 0` on an index actually takes: at
even `n` it yields `(2 : R) ≠ 0`.
-/

public section

namespace Int

/-- **An even integer whose cast is nonzero forces the cast of `2` to be nonzero**: it is `2` times
something, so a vanishing `2` would make it vanish too. -/
theorem two_ne_zero_of_even_of_cast_ne_zero {R : Type*} [NonAssocRing R] {n : ℤ} (heven : Even n)
    (h : (n : R) ≠ 0) : ((2 : ℤ) : R) ≠ 0 := by
  obtain ⟨m, rfl⟩ := heven
  intro h₀
  refine h ?_
  push_cast at h₀ ⊢
  rw [← two_mul, h₀, zero_mul]

end Int

end
