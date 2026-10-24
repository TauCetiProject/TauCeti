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

It also records that a point `x` lies on the segment from `a` to any point `lineMap a x T` with
`1 ≤ T` beyond `x` on the ray from `a` (`TauCeti.mem_segment_lineMap_of_one_le`).
-/

public section

open Set

namespace TauCeti

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

/-- A point `x` lies on the segment from `a` to any point `lineMap a x T` with `1 ≤ T`, that is,
to any point at or beyond `x` on the ray from `a` through `x`. -/
theorem mem_segment_lineMap_of_one_le {T : 𝕜} (hT : 1 ≤ T) :
    x ∈ segment 𝕜 a (AffineMap.lineMap a x T) := by
  rw [segment_eq_image_lineMap]
  refine ⟨T⁻¹, ⟨inv_nonneg.2 (zero_le_one.trans hT), inv_le_one_of_one_le₀ hT⟩, ?_⟩
  rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ (zero_lt_one.trans_le hT).ne',
    AffineMap.lineMap_apply_one]

end TauCeti
