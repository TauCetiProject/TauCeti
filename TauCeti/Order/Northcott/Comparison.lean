/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Order.Northcott

/-!
# Northcott functions under comparison

A function `h : α → β` is Northcott (Mathlib's `Northcott`) when each sublevel set
`{a | h a ≤ b}` is finite. This file records how the property moves between two functions that
are compared up to an additive constant.

* `Northcott.of_le_add`: if `h ≤ g + C` and `h` is Northcott, then so is `g`, because each
  sublevel set of `g` lies in a sublevel set of `h`.
* `northcott_iff_of_abs_sub_le`: two functions at uniformly bounded distance are Northcott
  together.

Heights attached to the same object are typically only defined up to a bounded function, and these
lemmas are what make finiteness of bounded-height sets independent of that choice.

## References

* A. J. de Jong, *Notes on Heights*, §17,
  <https://www.math.columbia.edu/~dejong/courses/heights.pdf>.
-/

public section

variable {α β : Type*}

namespace Northcott

/-- **Northcott transfers along a lower comparison.** If `h a ≤ g a + C` for every `a` and `h` is
Northcott, then `g` is Northcott: the sublevel set `{g ≤ b}` lies inside `{h ≤ b + C}`.
The comparison cannot be reversed: `0 ≤ n` on `ℕ`, yet the zero function is not Northcott. -/
theorem of_le_add [Preorder β] [Add β] [AddRightMono β] {h g : α → β} [Northcott h] (C : β)
    (hle : ∀ a, h a ≤ g a + C) : Northcott g where
  finite_le b := (finite_le (h := h) (b + C)).subset fun a (ha : g a ≤ b) ↦
    (hle a).trans (add_le_add_left ha C)

end Northcott

/-- **Functions at bounded distance are Northcott together.** If `|h a - g a| ≤ C` for every
`a`, then `h` is Northcott exactly when `g` is. -/
theorem northcott_iff_of_abs_sub_le [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]
    {h g : α → β} (C : β) (hC : ∀ a, |h a - g a| ≤ C) : Northcott h ↔ Northcott g := by
  refine ⟨fun _ ↦ Northcott.of_le_add (h := h) C fun a ↦ ?_,
    fun _ ↦ Northcott.of_le_add (h := g) C fun a ↦ ?_⟩
  · exact sub_le_iff_le_add'.1 (abs_sub_le_iff.1 (hC a)).1
  · exact sub_le_iff_le_add'.1 (abs_sub_le_iff.1 (hC a)).2

end
