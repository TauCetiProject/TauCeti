/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Fintype.Lattice

/-!
# Uniform margins for finitely many strict inequalities

In a nontrivial linearly ordered additive group, finitely many strict inequalities `f i < g i`
hold with a common positive margin `δ`: `f i + δ ≤ g i` for every `i`. For a nonempty index type
the margin is the least gap `g i - f i`; for an empty one any positive element works.

## Main results

* `TauCeti.exists_pos_forall_add_le_of_forall_lt`: finitely many strict inequalities hold with a
  uniform positive margin.
-/

public section

namespace TauCeti

variable {ι α : Type*} [Finite ι] [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  [Nontrivial α]

/-- Finitely many strict inequalities `f i < g i` hold with a uniform positive margin:
`f i + δ ≤ g i` for some `δ > 0` and every `i`. -/
theorem exists_pos_forall_add_le_of_forall_lt {f g : ι → α} (h : ∀ i, f i < g i) :
    ∃ δ > 0, ∀ i, f i + δ ≤ g i := by
  cases isEmpty_or_nonempty ι
  · obtain ⟨δ, hδ⟩ := exists_zero_lt (α := α)
    exact ⟨δ, hδ, isEmptyElim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i ↦ g i - f i
    exact ⟨g i₀ - f i₀, sub_pos.2 (h i₀), fun i ↦ le_sub_iff_add_le'.1 (hi₀ i)⟩

end TauCeti
