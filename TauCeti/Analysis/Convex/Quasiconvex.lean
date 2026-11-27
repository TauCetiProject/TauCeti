/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex

/-!
# Quasiconvex functions on segments

A function quasiconvex on `s` is bounded on each segment between two points of `s` by the larger
of its values at the endpoints (`QuasiconvexOn.le_max_of_mem_segment`), and in a linearly ordered
field likewise on each interval `[x, z]` with `x, z ∈ s` (`QuasiconvexOn.le_max_of_mem_Icc`).
These are the quasiconvex counterparts of Mathlib's `ConvexOn.le_max_of_mem_segment` and
`ConvexOn.le_max_of_mem_Icc`.
-/

public section

/-- A quasiconvex function is bounded on a segment by the larger of its values at the
endpoints. -/
theorem QuasiconvexOn.le_max_of_mem_segment {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [LinearOrder β] {s : Set E} {f : E → β} {x y z : E}
    (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hy : y ∈ segment 𝕜 x z) :
    f y ≤ max (f x) (f z) :=
  ((hf (max (f x) (f z))).segment_subset ⟨hx, le_max_left _ _⟩ ⟨hz, le_max_right _ _⟩ hy).2

/-- A function quasiconvex on a set `s` of a linearly ordered field is bounded on an interval
`[x, z]` with `x, z ∈ s` by the larger of its values at the endpoints. -/
theorem QuasiconvexOn.le_max_of_mem_Icc {𝕜 β : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [LinearOrder β] {s : Set 𝕜} {f : 𝕜 → β} {x y z : 𝕜}
    (hf : QuasiconvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hy : y ∈ Set.Icc x z) :
    f y ≤ max (f x) (f z) :=
  hf.le_max_of_mem_segment hx hz (Icc_subset_segment hy)
