/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Order.Bounds.Basic

/-!
# Bounded perturbations of bounded-range functions in ordered groups

In an ordered group, if `range f` is bounded below (respectively above) and the pointwise quotient
`f i / g i` (respectively `g i / f i`) is bounded above, then `range g` is bounded below
(respectively above). In a linearly ordered commutative group, a uniform bound on `|g i / f i|ₘ`
therefore preserves both `BddBelow` and `BddAbove` of `Set.range`.

## Main results

* `BddBelow.range_of_div_le` / `BddBelow.range_of_sub_le`: `BddBelow (range f)` is preserved when
  `f i / g i ≤ c` (additively `f i - g i ≤ c`) for all `i`.
* `BddAbove.range_of_div_le` / `BddAbove.range_of_sub_le`: `BddAbove (range f)` is preserved when
  `g i / f i ≤ c` (additively `g i - f i ≤ c`) for all `i`.
* `BddBelow.range_of_mabs_div_le` / `BddBelow.range_of_abs_sub_le` and
  `BddAbove.range_of_mabs_div_le` / `BddAbove.range_of_abs_sub_le`: two-sided uniform bounds
  `|g i / f i|ₘ ≤ c` (additively `|g i - f i| ≤ c`) preserve `BddBelow` and `BddAbove` of
  `Set.range`.
-/

public section

open Set

variable {ι : Sort*} {G : Type*}

section Group

variable [Group G] [Preorder G] [MulLeftMono G] [MulRightMono G] {f g : ι → G} {c : G}

/-- If `range f` is bounded below and `f i / g i ≤ c` for all `i`, then `range g` is bounded
below. -/
@[to_additive /-- If `range f` is bounded below and `f i - g i ≤ c` for all `i`, then `range g` is
bounded below. -/]
theorem BddBelow.range_of_div_le (hf : BddBelow (range f)) (hfg : ∀ i, f i / g i ≤ c) :
    BddBelow (range g) := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨c⁻¹ * b, forall_mem_range.2 fun i ↦
    inv_mul_le_iff_le_mul.2 ((hb (mem_range_self i)).trans (div_le_iff_le_mul.1 (hfg i)))⟩

/-- If `range f` is bounded above and `g i / f i ≤ c` for all `i`, then `range g` is bounded
above. -/
@[to_additive /-- If `range f` is bounded above and `g i - f i ≤ c` for all `i`, then `range g` is
bounded above. -/]
theorem BddAbove.range_of_div_le (hf : BddAbove (range f)) (hfg : ∀ i, g i / f i ≤ c) :
    BddAbove (range g) := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨c * b, forall_mem_range.2 fun i ↦
    (div_le_iff_le_mul.1 (hfg i)).trans ((mul_le_mul_iff_left c).2 (hb (mem_range_self i)))⟩

end Group

section LinearOrderedCommGroup

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {f g : ι → G} {c : G}

/-- If `range f` is bounded below and `|g i / f i|ₘ ≤ c` for all `i`, then `range g` is bounded
below. -/
@[to_additive /-- If `range f` is bounded below and `|g i - f i| ≤ c` for all `i`, then `range g`
is bounded below. -/]
theorem BddBelow.range_of_mabs_div_le (hf : BddBelow (range f)) (hfg : ∀ i, |g i / f i|ₘ ≤ c) :
    BddBelow (range g) :=
  hf.range_of_div_le fun i ↦ (mabs_div_le_iff.1 (hfg i)).2

/-- If `range f` is bounded above and `|g i / f i|ₘ ≤ c` for all `i`, then `range g` is bounded
above. -/
@[to_additive /-- If `range f` is bounded above and `|g i - f i| ≤ c` for all `i`, then `range g`
is bounded above. -/]
theorem BddAbove.range_of_mabs_div_le (hf : BddAbove (range f)) (hfg : ∀ i, |g i / f i|ₘ ≤ c) :
    BddAbove (range g) :=
  hf.range_of_div_le fun i ↦ (mabs_div_le_iff.1 (hfg i)).1

end LinearOrderedCommGroup
