/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character

/-!
# Characters at powers

The traces of the powers of `ρ g` are the character values at the powers of `g`:
`tr (ρ g ^ j) = χ_ρ (g ^ j)`.
-/

public section

namespace Representation

/-- The traces of the powers of `ρ g` are the character values at the powers of `g`. -/
theorem trace_pow_eq_character_pow {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (g : G) (j : ℕ) :
    LinearMap.trace k V (ρ g ^ j) = ρ.character (g ^ j) := by
  rw [character, map_pow ρ]

end Representation
