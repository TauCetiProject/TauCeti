/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Order.Filter.Defs

import Mathlib.Order.Filter.Basic

/-!
# Eventual inequalities under inversion and negation

Pointwise inversion in an ordered group (respectively negation in an ordered additive group)
reverses eventual inequalities along a filter (`Filter.EventuallyLE.inv` and
`Filter.EventuallyLE.neg`).
-/

public section

namespace Filter.EventuallyLE

variable {α β : Type*} [Group β] [LE β] [MulLeftMono β] [MulRightMono β]
  {l : Filter α} {f g : α → β}

/-- Inversion reverses eventual pointwise inequalities along a filter. -/
@[to_additive (attr := gcongr)
  /-- Negation reverses eventual pointwise inequalities along a filter. -/]
theorem inv (h : f ≤ᶠ[l] g) : g⁻¹ ≤ᶠ[l] f⁻¹ :=
  h.mono fun _ ↦ inv_le_inv_iff.mpr

end Filter.EventuallyLE
