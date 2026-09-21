/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Basic.Countable.Defs

/-!
# The units of a countable monoid are countable

Mathlib has `Finite αˣ` for a finite monoid (`Mathlib/Algebra/GroupWithZero/Units/Fintype.lean`)
but no countable analogue, so `Countable Mˣ` does not resolve even when `M` is countable. Both
follow the same way, from `Units.val` being injective.

## Main results

* `Units.instCountable`: `Mˣ` is countable whenever `M` is.
-/

public section

variable {M : Type*} [Monoid M]

/-- The units of a countable monoid form a countable type, since `Units.val` is injective.

This is the countable analogue of Mathlib's `Finite αˣ`, and is proved the same way. Without it
`Countable Mˣ` fails to synthesize, which in turn blocks `Countable (GL n R)` for a countable
ring `R` — `GL n R` is by definition `(Matrix n n R)ˣ`. -/
instance Units.instCountable [Countable M] : Countable Mˣ :=
  Function.Injective.countable Units.val_injective
