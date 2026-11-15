/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Order.Filter.Basic

/-!
# Eventual positive parts along a filter

A function that is eventually nonnegative along a filter agrees eventually with its positive part
(`Filter.EventuallyLE.posPart_eq`).
-/

public section

namespace Filter.EventuallyLE

variable {α β : Type*} [Lattice β] [DivInvMonoid β] {l : Filter α} {f : α → β}

/-- A function eventually bounded below by `1` agrees eventually with its `oneLePart`. -/
@[to_additive /-- An eventually nonnegative function agrees eventually with its positive part. -/]
theorem oneLePart_eq (hf : 1 ≤ᶠ[l] f) : f⁺ᵐ =ᶠ[l] f :=
  hf.mono fun _ ↦ oneLePart_eq_self.2

end Filter.EventuallyLE
