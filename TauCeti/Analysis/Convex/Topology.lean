/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology

/-!
# Topological properties of convex sets and segment unions

A convex set symmetric about the origin has `0` in its interior as soon as its interior is
nonempty. This lets volume arguments obtain the neighbourhood of the origin needed to use the
gauge of a symmetric convex set.

The interior of a sum of two convex sets with nonempty interiors is the sum of their
interiors. In particular, this describes the interior of the sum of two interval supports.

For segments `[x₀, x]` from a fixed apex `x₀` in a topological module over an ordered ring with
compact closed intervals, the union `⋃ x ∈ K, segment 𝕜 x₀ x` over a compact set `K` is compact
(`IsCompact.biUnion_segment`), and if a closed set `C` misses `⋃ x ∈ s, segment 𝕜 x₀ x` for an
arbitrary set `s`, then `C` also misses `[x₀, y]` for all `y` in a neighbourhood of `s`
(`IsClosed.eventually_disjoint_segment`).
-/

public section

open Filter Set
open scoped Pointwise Topology

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

section Segments

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [CompactIccSpace 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]

/-- The union of segments `[x₀, x]` from a fixed point `x₀` to the points of a compact set is
compact. -/
theorem IsCompact.biUnion_segment {K : Set E} (hK : IsCompact K) (x₀ : E) :
    IsCompact (⋃ x ∈ K, segment 𝕜 x₀ x) := by
  have heq : (⋃ x ∈ K, segment 𝕜 x₀ x) =
      (fun p : E × 𝕜 ↦ AffineMap.lineMap x₀ p.1 p.2) '' (K ×ˢ Icc (0 : 𝕜) 1) := by
    ext z
    simp only [mem_iUnion, exists_prop, segment_eq_image_lineMap, mem_image, Prod.exists, mem_prod]
    exact ⟨fun ⟨x, hx, t, ht, hxt⟩ ↦ ⟨x, t, ⟨hx, ht⟩, hxt⟩,
      fun ⟨x, t, ⟨hx, ht⟩, hxt⟩ ↦ ⟨x, hx, t, ht, hxt⟩⟩
  rw [heq]
  exact (hK.prod isCompact_Icc).image (by fun_prop)

/-- If a closed set `C` is disjoint from every segment `[x₀, x]` for `x ∈ s`, then `C` is disjoint
from `[x₀, y]` for all `y` in a neighbourhood of `s`, with no compactness assumption on `s` or
`C`. -/
theorem IsClosed.eventually_disjoint_segment {x₀ : E} {C s : Set E} (hC : IsClosed C)
    (h : Disjoint C (⋃ x ∈ s, segment 𝕜 x₀ x)) :
    ∀ᶠ y in 𝓝ˢ s, Disjoint C (segment 𝕜 x₀ y) := by
  have hO : IsOpen ((fun p : E × 𝕜 ↦ AffineMap.lineMap x₀ p.1 p.2) ⁻¹' Cᶜ) :=
    hC.isOpen_compl.preimage (by fun_prop)
  rw [eventually_iff_exists_mem]
  refine ⟨{y : E | Disjoint C (segment 𝕜 x₀ y)}, ?_, fun _ hy ↦ hy⟩
  rw [mem_nhdsSet_iff_forall]
  intro x hxs
  have hsub : ({x} : Set E) ×ˢ Icc (0 : 𝕜) 1 ⊆
      (fun p : E × 𝕜 ↦ AffineMap.lineMap x₀ p.1 p.2) ⁻¹' Cᶜ := by
    rintro ⟨y, t⟩ ⟨rfl : y = x, ht⟩ hmem
    exact h.le_bot ⟨hmem, mem_iUnion₂.2 ⟨y, hxs, lineMap_mem_segment 𝕜 x₀ y ht⟩⟩
  obtain ⟨u, v, huo, -, hxu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hO hsub
  refine Filter.mem_of_superset (huo.mem_nhds (hxu (mem_singleton x))) fun y hy ↦
    disjoint_left.2 fun z hzC hzseg ↦ ?_
  rcases segment_eq_image_lineMap 𝕜 x₀ y ▸ hzseg with ⟨t, ht, rfl⟩
  exact huv (mk_mem_prod hy (hv ht)) hzC

end Segments
