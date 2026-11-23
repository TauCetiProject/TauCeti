/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Interval reflection in ordered additive commutative groups

Subtracting from the right endpoint `b` reflects `[a, b]` to `[0, b - a]`, and similarly for the
open and half-open intervals `(a, b)`, `[a, b)`, and `(a, b]`.
-/

public section

namespace Set

section OrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c : α}

/-- Reflecting `c` across `b` maps `[0, b - a]` onto `[a, b]`. -/
theorem sub_mem_Icc_iff_mem_Icc_zero_sub : b - c ∈ Icc a b ↔ c ∈ Icc 0 (b - a) := by
  rw [sub_mem_Icc_iff_right, sub_self]

/-- Reflecting `c` across `b` maps `(0, b - a)` onto `(a, b)`. -/
theorem sub_mem_Ioo_iff_mem_Ioo_zero_sub : b - c ∈ Ioo a b ↔ c ∈ Ioo 0 (b - a) := by
  rw [sub_mem_Ioo_iff_right, sub_self]

/-- Reflecting `c` across `b` maps `(0, b - a]` onto `[a, b)`. -/
theorem sub_mem_Ico_iff_mem_Ioc_zero_sub : b - c ∈ Ico a b ↔ c ∈ Ioc 0 (b - a) := by
  rw [sub_mem_Ico_iff_right, sub_self]

/-- Reflecting `c` across `b` maps `[0, b - a)` onto `(a, b]`. -/
theorem sub_mem_Ioc_iff_mem_Ico_zero_sub : b - c ∈ Ioc a b ↔ c ∈ Ico 0 (b - a) := by
  rw [sub_mem_Ioc_iff_right, sub_self]

end OrderedAddCommGroup

end Set
