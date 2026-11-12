/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Sets.Compacts
public import TauCeti.Analysis.Convex.Join

/-!
# Interiors of convex sets

A convex set symmetric about the origin has `0` in its interior as soon as its interior is
nonempty. This lets volume arguments obtain the neighbourhood of the origin needed to use the
gauge of a symmetric convex set.

The interior of a sum of two convex sets with nonempty interiors is the sum of their
interiors. In particular, this describes the interior of the sum of two interval supports.

A closed segment `segment 𝕜 x y` is compact, being the continuous image of `Icc 0 1`.
More generally, the convex join of two compact sets is compact (`IsCompact.convexJoin`). So every
compact set `K` lies in a compact set star-convex about any given point `y`, the union of the
segments from `y` to `y` and to the points of `K` (`TopologicalSpace.Compacts.starHull`).
-/

public section

open Set
open scoped Pointwise

/-- The interior of a sum of convex sets with nonempty interiors is the sum of their
interiors. -/
theorem Convex.interior_add {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {s t : Set E} (hs : Convex 𝕜 s)
    (ht : Convex 𝕜 t) (hsne : (interior s).Nonempty) (htne : (interior t).Nonempty) :
    interior (s + t) = interior s + interior t := by
  have hopen : IsOpen (interior s + interior t) := isOpen_interior.add_left
  have hne : (interior (interior s + interior t)).Nonempty := by
    rw [hopen.interior_eq]
    exact add_nonempty.mpr ⟨hsne, htne⟩
  have hs' : s ⊆ closure (interior s) := by
    rw [hs.closure_interior_eq_closure_of_nonempty_interior hsne]
    exact subset_closure
  have ht' : t ⊆ closure (interior t) := by
    rw [ht.closure_interior_eq_closure_of_nonempty_interior htne]
    exact subset_closure
  have hsub : s + t ⊆ closure (interior s + interior t) := by
    rw [← add_image_prod, ← add_image_prod]
    exact (image_mono (Set.prod_mono hs' ht')).trans (by
      rw [← closure_prod_eq]
      exact image_closure_subset_closure_image (continuous_fst.add continuous_snd))
  refine subset_antisymm ?_ subset_interior_add
  calc
    interior (s + t) ⊆ interior (closure (interior s + interior t)) := interior_mono hsub
    _ = interior s + interior t := by
      rw [(hs.interior.add ht.interior).interior_closure_eq_interior_of_nonempty_interior hne,
        hopen.interior_eq]

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

namespace TauCeti

/-- A closed segment is compact: it is the continuous image of `Icc 0 1`. -/
theorem isCompact_segment (𝕜 : Type*) {E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
    [TopologicalSpace 𝕜] [CompactIccSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] (x y : E) :
    IsCompact (segment 𝕜 x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

end TauCeti

/-- The convex join of two compact sets is compact: it is the image of `s ×ˢ t ×ˢ [0, 1]` under
`((a, b), θ) ↦ a + θ • (b - a)`. -/
theorem IsCompact.convexJoin {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
    [TopologicalSpace 𝕜] [CompactIccSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin 𝕜 s t) := by
  have : _root_.convexJoin 𝕜 s t = (fun p : (E × E) × 𝕜 ↦ p.1.1 + p.2 • (p.1.2 - p.1.1)) ''
      ((s ×ˢ t) ×ˢ Icc 0 1) := by
    ext x
    simp only [mem_convexJoin, segment_eq_image', mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, θ, hθ, rfl⟩
      exact ⟨a, b, θ, ⟨⟨ha, hb⟩, hθ⟩, rfl⟩
    · rintro ⟨a, b, θ, ⟨⟨ha, hb⟩, hθ⟩, rfl⟩
      exact ⟨a, ha, b, hb, θ, hθ, rfl⟩
  rw [this]
  exact ((hs.prod ht).prod isCompact_Icc).image (by fun_prop)

namespace TopologicalSpace.Compacts

variable (𝕜 : Type*) {E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [CompactIccSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] (y : E) (K : Compacts E)

/-- The star hull of a compact set `K` about `y`: the union of the segments from `y` to `y` and to
the points of `K`. It is a compact set containing `y` and `K` and star-convex about `y`. -/
def starHull : Compacts E :=
  ⟨convexJoin 𝕜 {y} (insert y K), isCompact_singleton.convexJoin (K.isCompact.insert y)⟩

@[simp]
theorem coe_starHull : (K.starHull 𝕜 y : Set E) = convexJoin 𝕜 {y} (insert y (K : Set E)) :=
  (rfl)

variable {𝕜 y K} in
/-- A point lies in the star hull of `K` about `y` if and only if it is `y` or lies on a segment
from `y` to a point of `K`. -/
theorem mem_starHull_iff {x : E} :
    x ∈ K.starHull 𝕜 y ↔ x = y ∨ ∃ z ∈ K, x ∈ segment 𝕜 y z := by
  rw [← SetLike.mem_coe, coe_starHull, convexJoin_singleton_left, mem_iUnion₂]
  simp [segment_same]

theorem insert_subset_starHull : insert y (K : Set E) ⊆ K.starHull 𝕜 y :=
  subset_convexJoin_right (singleton_nonempty y)

theorem mem_starHull_self : y ∈ K.starHull 𝕜 y :=
  insert_subset_starHull 𝕜 y K (mem_insert y _)

theorem le_starHull : K ≤ K.starHull 𝕜 y :=
  (subset_insert y _).trans (insert_subset_starHull 𝕜 y K)

theorem singleton_le_starHull : {y} ≤ K.starHull 𝕜 y :=
  singleton_le_iff.2 (mem_starHull_self 𝕜 y K)

theorem starConvex_starHull : StarConvex 𝕜 y (K.starHull 𝕜 y : Set E) :=
  TauCeti.starConvex_convexJoin_singleton_left y _

variable {𝕜 y K} in
/-- The star hull of `K` about `y` is the least set containing `y` and `K` and star-convex about
`y`. -/
theorem starHull_subset {s : Set E} (hs : StarConvex 𝕜 y s) (hy : y ∈ s) (hK : (K : Set E) ⊆ s) :
    (K.starHull 𝕜 y : Set E) ⊆ s := by
  rw [coe_starHull, convexJoin_singleton_left]
  exact iUnion₂_subset fun z hz ↦ hs.segment_subset (insert_subset hy hK hz)

end TopologicalSpace.Compacts
