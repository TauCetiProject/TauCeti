/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset

import Mathlib.Tactic.Group

/-!
# Products of double cosets in a two-cell decomposition

Suppose the group `G` is the union of a subgroup `B` and a single double coset `B n B` with
`n² ∈ B`, as happens for the Bruhat decomposition of a group of Lie rank one. Then left
multiplication by the big cell `B n B` sends a double coset `B w B`, with `w ∈ B` or `w ∈ n B`,
into the union of `B (n w) B` and `B w B`. This is the multiplication axiom of a Tits system of
rank one.

## Main statements

* `Subgroup.doubleCoset_mul_doubleCoset_subset_union`: in a two-cell decomposition
  `G = B ∪ B n B` with `n² ∈ B`, the product `(B n B) (B w B)` lies in `B (n w) B ∪ B w B`.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.1.
-/

public section

open scoped Pointwise

open DoubleCoset

namespace Subgroup

variable {G : Type*} [Group G]

/-- In the presence of a two-cell decomposition `G = B ∪ B n B` with `n² ∈ B`, left
multiplication of a cell `B w B`, where `w ∈ B` or `w ∈ n B`, by `B n B` produces at most
`B (n w) B` and `B w B`. -/
theorem doubleCoset_mul_doubleCoset_subset_union (B : Subgroup G) {n w : G} (hn : n * n ∈ B)
    (hw : w ∈ B ∨ n⁻¹ * w ∈ B) (hbruhat : ∀ g : G, g ∈ B ∨ g ∈ doubleCoset n B B) :
    doubleCoset n B B * doubleCoset w B B ⊆ doubleCoset (n * w) B B ∪ doubleCoset w B B := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_doubleCoset.mp hx
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := mem_doubleCoset.mp hy
  rcases hw with hw | hw
  · -- If `w ∈ B`, the product is `b₁ (n w) (w⁻¹ b₂ b₃ w b₄)`.
    refine Or.inl (mem_doubleCoset.mpr ⟨b₁, hb₁, w⁻¹ * (b₂ * b₃ * w * b₄),
      mul_mem (inv_mem hw) (mul_mem (mul_mem (mul_mem hb₂ hb₃) hw) hb₄), ?_⟩)
    group
  · -- If `w ∈ n B`, then `n w ∈ B`, and the two cells of `G` are `B (n w) B` and `B w B`.
    have hnw : n * w ∈ B := by
      simpa only [mul_assoc, mul_inv_cancel_left] using mul_mem hn hw
    rcases hbruhat (b₁ * n * b₂ * (b₃ * w * b₄)) with hz | hz
    · refine Or.inl (mem_doubleCoset.mpr ⟨_, mul_mem hz (inv_mem hnw), 1, one_mem _, ?_⟩)
      group
    · obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := mem_doubleCoset.mp hz
      refine Or.inr (mem_doubleCoset.mpr ⟨c₁, hc₁, (n⁻¹ * w)⁻¹ * c₂,
        mul_mem (inv_mem hw) hc₂, ?_⟩)
      dsimp only
      rw [hc]
      group

end Subgroup
