/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.IsBotOne

/-!
# Pointwise order and single-coordinate functions

When zero is the bottom element in each coordinate, a single-coordinate function is below
another function precisely when its value at the selected coordinate is below the other
function's value there.
-/

public section

namespace Pi

/-- Compare a single-coordinate function to another function by comparing their values at the
selected coordinate, when zero is the bottom element in each coordinate. -/
@[simp]
theorem single_le_iff {ι : Type*} {α : ι → Type*} [DecidableEq ι]
    [∀ i, Preorder (α i)] [∀ i, Zero (α i)] [∀ i, IsBotZeroClass (α i)]
    {i : ι} {a : α i} {f : ∀ j, α j} :
    Pi.single i a ≤ f ↔ a ≤ f i := by
  simp [Pi.single, update_le_iff]

end Pi
