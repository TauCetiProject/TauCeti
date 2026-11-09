/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Primitive additive characters

Mathlib's `AddChar.IsPrimitive` asks that every multiplicative shift of an additive character by a
nonzero element be nontrivial. Consumers that just need *some* nontrivial additive character —
character sums over a finite field, the cuspidal characters of `GL₂(F)` — want the weaker
statement that a primitive character differs from the trivial one, which is primitivity read at
the shift by `1`. Over a field the converse is Mathlib's `AddChar.IsPrimitive.of_ne_one`.

## Main results

* `AddChar.IsPrimitive.ne_one`: a primitive additive character on a nontrivial ring is
  nontrivial.
-/

public section

namespace AddChar

variable {R R' : Type*} [CommRing R] [Nontrivial R] [CommMonoid R']

/-- A primitive additive character on a nontrivial ring is nontrivial. -/
theorem IsPrimitive.ne_one {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) : ψ ≠ 1 := by
  simpa only [mulShift_one] using hψ one_ne_zero

end AddChar
