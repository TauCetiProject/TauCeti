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
`|G| ≤ B` on a function-valued `G` gives the bounds `Pi.single i B` for the family `Pi.single i G`.

## Main results

* `Pi.forall_single_of`: `Pi.single i x` inherits at every index any property shared by `x`
  and `0`.
* `Pi.abs_single_le_single`: a bound `|G| ≤ B` gives `|Pi.single i G j| ≤ Pi.single i B j`.
-/

public section

namespace Pi

variable {ι : Type*} [DecidableEq ι]

/-- The family `Pi.single i x` inherits, at every index, any property shared by `x` and `0`. This
is the `Pi.single` form of `Function.forall_update_iff`. -/
theorem forall_single_of {β : Type*} [Zero β] (i : ι) {p : β → Prop} (h₀ : p 0) {x : β}
    (hx : p x) : ∀ j, p ((single i x : ι → β) j) :=
  (Function.forall_update_iff (0 : ι → β) fun _ ↦ p).2 ⟨hx, fun _ _ ↦ h₀⟩

/-- A bound `|G| ≤ B` on a function `G` of two variables gives the bounds `Pi.single i B` for the
family `Pi.single i G`. -/
theorem abs_single_le_single {X Y α : Type*} [Lattice α] [AddGroup α] [AddLeftMono α] (i : ι)
    {G : X → Y → α} {B : α} (hB : ∀ t x, |G t x| ≤ B) :
    ∀ j t x, |(single i G : ι → X → Y → α) j t x| ≤ (single i B : ι → α) j := by
  intro j t x
  rcases eq_or_ne j i with rfl | hj
  · simpa using hB t x
  · simp [single_eq_of_ne hj]

end Pi
