/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Order-connected sets under inversion and negation

Inversion and negation preserve order-connectedness of sets in ordered groups.

## Main results

* `Set.OrdConnected.inv`: `I.OrdConnected → I⁻¹.OrdConnected`.
* `Set.OrdConnected.neg`: `I.OrdConnected → (-I).OrdConnected`.
-/

public section

namespace Set

open scoped Pointwise

/-- Inversion preserves order-connectedness in an ordered group. -/
@[to_additive /-- Negation preserves order-connectedness in an ordered additive group. -/]
theorem OrdConnected.inv {α : Type*} [Group α] [Preorder α] [MulLeftMono α] [MulRightMono α]
    {I : Set α} (hI : I.OrdConnected) : I⁻¹.OrdConnected :=
  hI.preimage_anti fun _ _ h ↦ inv_le_inv_iff.2 h

end Set
