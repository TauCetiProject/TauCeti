/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Interval membership under ordered subtraction

In a linearly ordered additive semigroup with ordered subtraction, shifting a left-open,
right-closed interval `Set.Ioc u v` by `x₀ ≤ u` reduces membership of `x₀ + z` in `Ioc u v`
to membership of `z` in `Ioc (u - x₀) (v - x₀)` without requiring `u ≤ v`.
-/

public section

namespace Set

/-- Shifting by `x₀ ≤ u` moves membership in `Ioc u v` to membership in `Ioc (u - x₀) (v - x₀)`.
No ordering between `u` and `v` is needed: both intervals are empty when `v ≤ u`. -/
theorem add_mem_Ioc_iff_tsub {α : Type*} [LinearOrder α] [AddCommSemigroup α]
    [ExistsAddOfLE α] [AddLeftMono α] [AddLeftReflectLE α] [Sub α] [OrderedSub α]
    {x₀ u v z : α} (hx : x₀ ≤ u) :
    x₀ + z ∈ Ioc u v ↔ z ∈ Ioc (u - x₀) (v - x₀) := by
  simp only [mem_Ioc, tsub_lt_iff_left hx]
  refine ⟨fun ⟨hu, hv⟩ => ⟨hu, le_tsub_of_add_le_left hv⟩, fun ⟨hu, hv⟩ => ⟨hu, ?_⟩⟩
  have hlt : u - x₀ < v - x₀ := ((tsub_lt_iff_left hx).mpr hu).trans_le hv
  exact (le_tsub_iff_left (hx.trans (lt_of_tsub_lt_tsub_right hlt).le)).mp hv

end Set
