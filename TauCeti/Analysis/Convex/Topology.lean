/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology

/-!
# Interior of symmetric convex sets

A convex set symmetric about the origin has `0` in its interior as soon as its interior is
nonempty. This lets volume arguments obtain the neighbourhood of the origin needed to use the
gauge of a symmetric convex set.
-/

public section

open Set

/-- A convex set symmetric about the origin with nonempty interior has the origin in its
interior. -/
theorem Convex.zero_mem_interior_of_symmetric {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] {s : Set E} (hs : Convex 𝕜 s)
    (hsymm : ∀ x ∈ s, -x ∈ s) (hi : (interior s).Nonempty) :
    (0 : E) ∈ interior s := by
  obtain ⟨x, hx⟩ := hi
  have hx' : -x ∈ interior s := (Homeomorph.neg E).isOpenMap.mapsTo_interior hsymm hx
  simpa using hs.interior hx hx' (by norm_num : (0 : 𝕜) ≤ 1 / 2)
    (by norm_num : (0 : 𝕜) ≤ 1 / 2) (by norm_num)
