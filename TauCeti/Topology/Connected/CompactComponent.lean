/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Regular

/-!
# Neighbourhoods of compact connected components of closed sets

Let `S` be a closed subset of a locally compact Hausdorff space `X`, and let `L` be the connected
component of a point `x` in `S`. If `L` is compact, it can be cut out of `S` by an open set: every
open `U ⊇ L` contains an open `V ⊇ L` with compact closure whose frontier does not meet `S`, that
is, `closure V ∩ S ⊆ V`
(`IsClosed.exists_isOpen_closure_inter_subset_of_isCompact_connectedComponentIn`). Equivalently,
`V ∩ S` is a clopen subset of `S` containing `L`.

The proof works in the compact Hausdorff space `K ∩ S`, for a compact neighbourhood `K` of `L`
inside `U`. There `L` is the connected component of `x`, hence the intersection of the clopen
sets containing `x` (`connectedComponent_eq_iInter_isClopen`), and by compactness a single clopen
set `A ∋ x` already lies in the interior of `K`. The sets `A` and `(K ∩ S) \ A` are disjoint
compact subsets of `X`, and `V` is an open neighbourhood of `A` with compact closure avoiding the
second one.

The typical use is a level set `S = F⁻¹(c)` of a continuous map: the values of `F` on the compact
frontier of `V` then stay away from `c`, and the points of `V` with values near `c` form an open
neighbourhood of `L` whose intersection with each nearby level is compact.

We also record that the connected component of `x` in `S` is unchanged when computed in a
subspace containing it (`Subtype.image_val_connectedComponentIn_preimage`).
-/

public section

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- If the connected component of `x` in `S` lies in the subspace `U`, then it is the image of the
connected component of `x` in the trace of `S` on `U`. -/
theorem Subtype.image_val_connectedComponentIn_preimage {U S : Set X} {x : U}
    (h : connectedComponentIn S x ⊆ U) :
    (↑) '' connectedComponentIn ((↑) ⁻¹' S : Set U) x = connectedComponentIn S x := by
  by_cases hx : (x : X) ∈ S
  · refine subset_antisymm ?_ ?_
    · exact (isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn)
        |>.subset_connectedComponentIn ⟨x, mem_connectedComponentIn hx, rfl⟩
          (image_subset_iff.2 (connectedComponentIn_subset _ _))
    · -- The component of `x` in `S` is a preconnected subset of `U`, so it is the image of a
      -- preconnected subset of `U` through `x` inside the trace of `S`.
      have hpre : IsPreconnected ((↑) ⁻¹' connectedComponentIn S x : Set U) := by
        rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
          inter_eq_right.2 h]
        exact isPreconnected_connectedComponentIn
      have hsub := hpre.subset_connectedComponentIn (mem_connectedComponentIn hx)
        (preimage_mono (connectedComponentIn_subset _ _))
      calc connectedComponentIn S x = (↑) '' ((↑) ⁻¹' connectedComponentIn S x : Set U) := by
            rw [Subtype.image_preimage_coe, inter_eq_right.2 h]
        _ ⊆ _ := image_mono hsub
  · rw [connectedComponentIn_eq_empty hx,
      connectedComponentIn_eq_empty (by rwa [mem_preimage] : x ∉ ((↑) ⁻¹' S : Set U)),
      image_empty]

variable [T2Space X] [LocallyCompactSpace X]

/-- **Compact components of closed sets are cut out by open sets.** In a locally compact
Hausdorff space, let the connected component `L` of `x` in a closed set `S` be compact. Then every
open `U ⊇ L` contains an open `V ⊇ L` with compact closure such that `closure V ∩ S ⊆ V`: the
frontier of `V` does not meet `S`, so `V ∩ S` is clopen in `S`. -/
theorem IsClosed.exists_isOpen_closure_inter_subset_of_isCompact_connectedComponentIn {S U : Set X}
    (hS : IsClosed S) {x : X} (hL : IsCompact (connectedComponentIn S x)) (hU : IsOpen U)
    (hLU : connectedComponentIn S x ⊆ U) :
    ∃ V, IsOpen V ∧ connectedComponentIn S x ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) ∧
      closure V ∩ S ⊆ V := by
  by_cases hx : x ∈ S
  swap
  · exact ⟨∅, isOpen_empty, by simp [connectedComponentIn_eq_empty hx], by simp, by simp,
      by simp⟩
  obtain ⟨K, hK, hLK, hKU⟩ := exists_compact_between hL hU hLU
  have hxK : x ∈ K := interior_subset (hLK (mem_connectedComponentIn hx))
  have : CompactSpace (K ∩ S : Set X) := isCompact_iff_compactSpace.1 (hK.inter_right hS)
  set x' : (K ∩ S : Set X) := ⟨x, hxK, hx⟩
  -- The component of `x` in `S` is the component of `x` in the compact space `K ∩ S`.
  have hsub : connectedComponentIn S x ⊆ connectedComponentIn (K ∩ S) x :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hx)
      fun y hy ↦ ⟨interior_subset (hLK hy), connectedComponentIn_subset _ _ hy⟩
  have hLT : connectedComponentIn S x = (↑) '' connectedComponent x' :=
    (subset_antisymm hsub (connectedComponentIn_mono _ inter_subset_right)).trans
      (connectedComponentIn_eq_image (⟨hxK, hx⟩ : x ∈ K ∩ S))
  -- A single clopen subset `A ∋ x` of `K ∩ S` lies in the interior of `K`, since the
  -- intersection of all of them is the component of `x`.
  obtain ⟨A, hA, hxA, hAK⟩ : ∃ A : Set (K ∩ S : Set X), IsClopen A ∧ x' ∈ A ∧
      ∀ y ∈ A, (y : X) ∈ interior K := by
    have hC : IsClosed {y : (K ∩ S : Set X) | (y : X) ∉ interior K} :=
      (isOpen_interior.preimage continuous_subtype_val).isClosed_compl
    have hdisj : Disjoint {y : (K ∩ S : Set X) | (y : X) ∉ interior K}
        (⋂ s : {s : Set (K ∩ S : Set X) // IsClopen s ∧ x' ∈ s}, (s : Set _)) := by
      rw [← connectedComponent_eq_iInter_isClopen, disjoint_left]
      exact fun y hy hyc ↦ hy (hLK (hLT ▸ mem_image_of_mem _ hyc))
    obtain ⟨u, hu⟩ := hC.isCompact.elim_finite_subfamily_closed
      (fun s : {s : Set (K ∩ S : Set X) // IsClopen s ∧ x' ∈ s} ↦ (s : Set _))
      (fun s ↦ s.2.1.1) hdisj
    refine ⟨⋂ s ∈ u, (s : Set (K ∩ S : Set X)), isClopen_biInter_finset fun s _ ↦ s.2.1,
      mem_iInter₂.2 fun s _ ↦ s.2.2, fun y hy ↦ ?_⟩
    by_contra hyK
    exact disjoint_left.1 hu hyK hy
  -- Separate the compact set `A` from the compact set `(K ∩ S) \ A` by an open set `V` with
  -- compact closure inside the interior of `K`.
  have hA' : IsCompact ((↑) '' A : Set X) := hA.isClosed.isCompact.image continuous_subtype_val
  have hB' : IsClosed ((↑) '' Aᶜ : Set X) :=
    (hA.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
  obtain ⟨V, hV, hAV, hVsub, hVc⟩ := exists_open_between_and_isCompact_closure hA'
    (isOpen_interior.sdiff hB') (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hAK y hy, ?_⟩
      rintro ⟨z, hz, hzy⟩
      exact hz (Subtype.ext hzy ▸ hy))
  refine ⟨V, hV, ?_, hVsub.trans (sdiff_subset.trans (interior_subset.trans hKU)), hVc, ?_⟩
  · rw [hLT]
    rintro _ ⟨y, hy, rfl⟩
    exact hAV ⟨y, hA.connectedComponent_subset hxA hy, rfl⟩
  · rintro y ⟨hyV, hyS⟩
    have hyK : y ∈ K := interior_subset (hVsub hyV).1
    by_cases hy : (⟨y, hyK, hyS⟩ : (K ∩ S : Set X)) ∈ A
    · exact hAV ⟨_, hy, rfl⟩
    · exact absurd ⟨_, hy, rfl⟩ (hVsub hyV).2
