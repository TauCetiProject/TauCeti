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

Mathlib provides `Finite αˣ` for a finite monoid
(`Mathlib/Algebra/GroupWithZero/Units/Fintype.lean`) but no countable analogue, so `Countable Mˣ`
does not synthesize even when `M` is countable. This file supplies it, together with the additive
version for `AddUnits`.

## Main results

* `Units.instCountable`: `Mˣ` is countable whenever `M` is.
* `AddUnits.instCountable`: `AddUnits M` is countable whenever `M` is.
-/

public section

variable {M : Type*} [Monoid M]

/-- The units of a countable monoid form a countable type.

This is the countable analogue of Mathlib's `Finite αˣ`. Since `GL n R` is by definition
`(Matrix n n R)ˣ`, it gives `Countable (GL n R)` whenever the matrix ring is countable. -/
@[to_additive /-- The additive units of a countable additive monoid form a countable type. -/]
instance Units.instCountable [Countable M] : Countable Mˣ :=
  Units.val_injective.countable
