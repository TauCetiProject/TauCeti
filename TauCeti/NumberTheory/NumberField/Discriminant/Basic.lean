/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Basic facts about the discriminant of a number field

The discriminant of a number field is a nonzero integer (Mathlib's `NumberField.discr_ne_zero`), so
its absolute value is a nonzero natural number. This is recorded as a `NeZero` instance, which
lets `(discr K).natAbs` serve as the level of a Dirichlet character whose `L`-function is taken,
such as the quadratic character of a quadratic field.

## Main results

* `NumberField.instNeZeroNatAbsDiscr`: `(discr K).natAbs ≠ 0`, as a `NeZero` instance.
-/

public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute value of the discriminant of a number field is a nonzero level, as the
`L`-function of a Dirichlet character of that level requires. -/
instance instNeZeroNatAbsDiscr : NeZero (discr K).natAbs :=
  ⟨Int.natAbs_ne_zero.mpr (discr_ne_zero K)⟩

end NumberField
