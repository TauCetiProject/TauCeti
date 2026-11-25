/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Basic.Countable.Defs

/-!
# `Countable` is preserved by `Additive` and `Multiplicative`

Mathlib provides `Finite (Additive α)` and `Finite (Multiplicative α)` in
`Mathlib/Algebra/Group/TypeTags/Finite.lean`, but no `Countable` counterparts. This file supplies
those instances.

## Main results

* `Additive.instCountable`: `Additive α` is countable whenever `α` is.
* `Multiplicative.instCountable`: `Multiplicative α` is countable whenever `α` is.
-/

public section

/-- `Additive` preserves countability. -/
instance Additive.instCountable {α : Type*} [Countable α] : Countable (Additive α) :=
  Additive.toMul.injective.countable

/-- `Multiplicative` preserves countability. -/
instance Multiplicative.instCountable {α : Type*} [Countable α] : Countable (Multiplicative α) :=
  Multiplicative.toAdd.injective.countable

end
