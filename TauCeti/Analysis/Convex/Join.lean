/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Join

/-!
# Convex hulls with a point adjoined

Mathlib's `convexHull_insert` writes the convex hull of `insert a s` as the convex join of `{a}`
with the convex hull of `s`, provided `s` is nonempty. This file states the membership form with
no nonemptiness hypothesis: a point of the convex hull of `insert a s` is either `a` itself or
lies on a segment from `a` to a point of the convex hull of `s` (`TauCeti.mem_convexHull_insert`).

The convex join of a point `x` with any set is star-convex about `x`
(`TauCeti.starConvex_convexJoin_singleton_left`). Consequently, if `s` is convex, `x ∈ t`, and `t`
is star-convex about every point of `s`, then `convexHull 𝕜 (insert x s) ⊆ t`
(`Convex.convexHull_insert_subset_of_forall_starConvex`).
-/

public section

open Set

namespace TauCeti

section LinearOrderedField

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {s : Set E} {a x : E}

/-- A point of the convex hull of `insert a s` is either `a` or lies on a segment from `a` to a
point of the convex hull of `s`. Unlike `convexHull_insert`, this needs no nonemptiness of `s`. -/
theorem mem_convexHull_insert :
    x ∈ convexHull 𝕜 (insert a s) ↔ x = a ∨ ∃ y ∈ convexHull 𝕜 s, x ∈ segment 𝕜 a y := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rw [convexHull_insert hs, convexJoin_singleton_left, mem_iUnion₂]
  refine ⟨fun ⟨y, hy, hxy⟩ => .inr ⟨y, hy, hxy⟩, ?_⟩
  rintro (rfl | ⟨y, hy, hxy⟩)
  · obtain ⟨y, hy⟩ := hs.convexHull (𝕜 := 𝕜)
    exact ⟨y, hy, left_mem_segment 𝕜 x y⟩
  · exact ⟨y, hy, hxy⟩

end LinearOrderedField

section OrderedSemiring

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E]
  [Module 𝕜 E]

/-- The convex join of `{x}` with any set, the union of the segments from `x` to its points, is
star-convex about `x`. -/
theorem starConvex_convexJoin_singleton_left (x : E) (t : Set E) :
    StarConvex 𝕜 x (convexJoin 𝕜 {x} t) := by
  rw [convexJoin_singleton_left]
  exact starConvex_iUnion₂ fun y _ ↦ (convex_segment x y).starConvex (left_mem_segment 𝕜 x y)

end OrderedSemiring

end TauCeti

/-- If `s` is convex, `x ∈ t`, and `t` is star-convex about every point of `s`, then the convex
hull of `insert x s` lies in `t`. -/
theorem Convex.convexHull_insert_subset_of_forall_starConvex {𝕜 E : Type*} [Field 𝕜]
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E} {x : E}
    (hs : Convex 𝕜 s) (hx : x ∈ t) (h : ∀ y ∈ s, StarConvex 𝕜 y t) :
    convexHull 𝕜 (insert x s) ⊆ t := by
  intro z hz
  rcases TauCeti.mem_convexHull_insert.1 hz with rfl | ⟨y, hy, hzy⟩
  · exact hx
  · rw [hs.convexHull_eq] at hy
    rw [segment_symm] at hzy
    exact (h y hy).segment_subset hx hzy

