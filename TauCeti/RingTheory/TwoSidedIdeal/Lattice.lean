/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Lattice lemmas for two-sided ideals

This file supplements Mathlib's `Mathlib.RingTheory.TwoSidedIdeal.Lattice` with basic lattice
characterizations for two-sided ideals.

## Main results

* `TwoSidedIdeal.ne_bot_iff`: a two-sided ideal is nonzero if and only if it contains a nonzero
  element.
-/

public section

namespace TwoSidedIdeal

/-- A two-sided ideal is nonzero if and only if it contains a nonzero element. -/
protected theorem ne_bot_iff {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R) :
    I ≠ ⊥ ↔ ∃ x ∈ I, x ≠ 0 := by
  rw [ne_eq, _root_.eq_bot_iff, IsConcreteLE.le_iff]
  simp [mem_bot]

end TwoSidedIdeal
