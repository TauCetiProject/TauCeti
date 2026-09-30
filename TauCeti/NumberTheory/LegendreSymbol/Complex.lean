/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Complex

/-!
# Nontriviality of the canonical complex additive character of a finite field

Mathlib's `AddChar.FiniteField.primitiveChar_to_Complex` is the canonical primitive additive
character of a finite field `F` with values in `ℂ`, and
`AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive` records its primitivity. Consumers
that just need *some* nontrivial additive character of `F` — character sums over `F`, the
cuspidal characters of `GL₂(F)` — want the weaker statement that it differs from the trivial
character, which is primitivity read at the shift by `1`.

## Main results

* `TauCeti.primitiveChar_to_Complex_ne_one`:
  `AddChar.FiniteField.primitiveChar_to_Complex F ≠ 1`.
-/

public section

namespace TauCeti

variable (F : Type*) [Field F] [Finite F]

/-- Mathlib's canonical primitive complex additive character of a finite field is nontrivial. -/
theorem primitiveChar_to_Complex_ne_one :
    AddChar.FiniteField.primitiveChar_to_Complex F ≠ 1 := by
  simpa only [AddChar.mulShift_one] using
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F (one_ne_zero : (1 : F) ≠ 0)

end TauCeti
