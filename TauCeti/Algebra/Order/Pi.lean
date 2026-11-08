/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-!
# Properties and bounds of `Pi.single` families

A family `Pi.single i x` is `x` at the index `i` and `0` at every other index. This file records
that such a family inherits, at every index, any property shared by `x` and `0`, and that a bound
`|x| ≤ b` gives the bounds `Pi.single i b` for the family `Pi.single i x`.

## Main results

* `Pi.forall_single_of`: `Pi.single i x` inherits at every index any property shared by `x`
  and `0`.
* `Pi.abs_single_le_single`: a bound `|x| ≤ b` gives `|Pi.single i x j| ≤ Pi.single i b j`.
-/

public section

namespace Pi

variable {ι : Type*} [DecidableEq ι]

/-- The family `Pi.single i x` inherits, at every index, any property shared by `x` and `0`. This
is the `Pi.single` form of `Function.forall_update_iff`. -/
theorem forall_single_of {β : Type*} [Zero β] (i : ι) {p : β → Prop} (h₀ : p 0) {x : β}
    (hx : p x) : ∀ j, p ((single i x : ι → β) j) :=
  (Function.forall_update_iff (0 : ι → β) fun _ ↦ p).2 ⟨hx, fun _ _ ↦ h₀⟩

/-- A bound `|x| ≤ b` gives the bounds `Pi.single i b` for the family `Pi.single i x`. -/
theorem abs_single_le_single {α : Type*} [Lattice α] [AddGroup α] [AddLeftMono α] (i : ι)
    {x b : α} (h : |x| ≤ b) (j : ι) : |(single i x : ι → α) j| ≤ (single i b : ι → α) j := by
  rcases eq_or_ne j i with rfl | hj
  · simpa using h
  · simp [single_eq_of_ne hj]

end Pi
