/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Preconnected sets: disjoint open covers and compact injective images

A preconnected set covered by a family of pairwise disjoint open sets lies in each member of the
family that it meets. This is the form in which connectedness is used to show that a region
contained in a union of disjoint open cells lies in a single cell.

Dually, when a preconnected set is the union of a locally finite family of closed sets, any two
nonempty members are joined by a chain of members in which consecutive sets meet
(`IsPreconnected.transGen_of_iUnion_of_isClosed`). For instance, the irreducible components of a
connected Noetherian space form a connected intersection graph.

The same principle selects a limit: a function which tends to a finite subset of a Hausdorff
space along a filter in which arbitrarily small sets have preconnected images tends to a single
point of that subset (`Filter.Tendsto.exists_mem_tendsto_nhds`). For instance, near a point
whose punctured neighbourhoods are connected, a continuous function approaching a finite set
chooses one of its points.

An open set is not preconnected exactly when it is the union of two disjoint nonempty open sets
(`IsOpen.not_isPreconnected_iff`), as for clopen sets in Mathlib.

A continuous injection on a compact set into a Hausdorff space is a closed embedding of that set,
so preconnectedness of the image is equivalent to preconnectedness of the set
(`IsCompact.isPreconnected_image_iff_of_injOn`).

A continuous function on a preconnected set that is locally constant near each point where it
takes a given value `f z`, for some `z` in the set, is constant
(`IsPreconnected.eqOn_const_of_eventually_eq`). This is how a strong maximum principle spreads
from a neighbourhood of a maximum point to the whole domain.

In a `T₁` space, the connected component `connectedComponentIn s x` of a point isolated in `s` is
the point itself (`TauCeti.connectedComponentIn_eq_singleton`): the component is covered by the
open sets `{x}ᶜ` and a neighbourhood of `x` meeting `s` only at `x`, whose intersection misses `s`.
-/

public section

open Filter Function Set Topology

variable {α ι : Type*} [TopologicalSpace α]

/-- A preconnected set covered by pairwise disjoint open sets `u i` lies in each `u i` that it
meets. -/
theorem IsPreconnected.subset_of_subset_iUnion {s : Set α} {u : ι → Set α}
    (hs : IsPreconnected s) (hu : ∀ i, IsOpen (u i)) (hdisj : Pairwise (Disjoint on u))
    (hsu : s ⊆ ⋃ i, u i) {i : ι} (hsi : (s ∩ u i).Nonempty) : s ⊆ u i := by
  classical
  refine hs.subset_left_of_subset_union (v := ⋃ (j) (_ : j ≠ i), u j) (hu i)
    (isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hu j)
    (disjoint_iUnion₂_right.2 fun j hj ↦ hdisj (Ne.symm hj)) (fun x hx ↦ ?_) hsi
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hsu hx)
  by_cases hji : j = i
  · exact Or.inl (hji ▸ hj)
  · exact Or.inr (mem_iUnion₂.2 ⟨j, hji, hj⟩)

/-- If the union of a locally finite family of closed sets `s i` is preconnected, any two nonempty
members are joined by a chain of members in which consecutive sets meet. This is the closed
counterpart of Mathlib's `IsPreconnected.transGen_of_iUnion` for open sets; local finiteness makes
the unions of subfamilies closed. -/
theorem IsPreconnected.transGen_of_iUnion_of_isClosed {s : ι → Set α} (hf : LocallyFinite s)
    (hs : IsPreconnected (⋃ n, s n)) (hs' : ∀ i, IsClosed (s i)) (i j : ι)
    (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    Relation.TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i j := by
  by_contra hij
  let S : Set ι := {k | Relation.TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i k}
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hiS : i ∈ S := Relation.TransGen.single ⟨a, ha, ha⟩
  have hcl (T : Set ι) : IsClosed (⋃ k ∈ T, s k) := by
    rw [biUnion_eq_iUnion]
    exact (hf.comp_injective Subtype.val_injective).isClosed_iUnion fun k ↦ hs' k
  -- The members reachable from `i` and the others give two closed sets covering the union.
  obtain ⟨x, -, hxU, hxV⟩ := isPreconnected_closed_iff.mp hs (⋃ k ∈ S, s k) (⋃ k ∈ Sᶜ, s k)
    (hcl S) (hcl Sᶜ) (iSup_split s (· ∈ S)).le
    ⟨a, mem_iUnion_of_mem i ha, mem_iUnion₂_of_mem hiS ha⟩
    ⟨b, mem_iUnion_of_mem j hb, mem_iUnion₂_of_mem hij hb⟩
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hxU
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.1 hxV
  exact hl (hk.tail ⟨x, hxk, hxl⟩)

/-- **Local constancy at a value spreads over a preconnected set.** Let `f` be continuous at each
point of a preconnected set `U` and `z ∈ U`. If `f` is identically `f z` near every point of `U`
at which it takes the value `f z`, then `f = f z` on all of `U`. -/
theorem IsPreconnected.eqOn_const_of_eventually_eq {β : Type*} [TopologicalSpace β] [T1Space β]
    {U : Set α} {f : α → β} {z : α} (hU : IsPreconnected U) (hz : z ∈ U)
    (hf : ∀ x ∈ U, ContinuousAt f x) (hlocal : ∀ x ∈ U, f x = f z → ∀ᶠ y in 𝓝 x, f y = f z) :
    EqOn f (const α (f z)) U := by
  -- The points near which `f` is identically `f z` form an open set, which is relatively closed
  -- in `U` by continuity and `hlocal`, and contains `z`.
  have hsubset : U ⊆ {x | ∀ᶠ y in 𝓝 x, f y = f z} := by
    refine hU.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds
      ⟨z, hz, hlocal z hz rfl⟩ ?_
    rintro x ⟨hxcl, hxU⟩
    refine hlocal x hxU (by_contra fun hxz ↦ ?_)
    obtain ⟨y, hy, hyO⟩ := mem_closure_iff_nhds.mp hxcl _
      ((hf x hxU).preimage_mem_nhds (isOpen_ne.mem_nhds hxz))
    exact hy hyO.self_of_nhds
  exact fun x hx ↦ (hsubset hx).self_of_nhds

/-- An open set is not preconnected exactly when it is the union of two disjoint nonempty open
sets. -/
theorem IsOpen.not_isPreconnected_iff {s : Set α} (hs : IsOpen s) :
    ¬ IsPreconnected s ↔
      ∃ a b, IsOpen a ∧ IsOpen b ∧ a.Nonempty ∧ b.Nonempty ∧ Disjoint a b ∧ s = a ∪ b := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp only [IsPreconnected, not_forall, not_nonempty_iff_eq_empty, exists_prop] at h
    obtain ⟨u, v, hu, hv, huv, hsu, hsv, hsuv⟩ := h
    exact ⟨s ∩ u, s ∩ v, hs.inter hu, hs.inter hv, hsu, hsv,
      disjoint_iff_inter_eq_empty.2 (by rw [inter_inter_inter_comm, inter_self, hsuv]),
      by rw [← inter_union_distrib_left, inter_eq_left.2 huv]⟩
  · rintro ⟨a, b, ha, hb, ⟨x, hx⟩, ⟨y, hy⟩, hab, rfl⟩ h
    obtain ⟨z, -, hza, hzb⟩ := h a b ha hb subset_rfl ⟨x, Or.inl hx, hx⟩ ⟨y, Or.inr hy, hy⟩
    exact disjoint_left.1 hab hza hzb

namespace TauCeti

/-- In a `T₁` space, a point isolated in a set `s` is its own connected component in `s`. -/
theorem connectedComponentIn_eq_singleton [T1Space α] {s : Set α} {x : α} (hx : x ∈ s)
    (hiso : ∀ᶠ z in 𝓝 x, z ∈ s → z = x) : connectedComponentIn s x = {x} := by
  obtain ⟨U, hUx, hU, hxU⟩ := eventually_nhds_iff.1 hiso
  refine (subset_singleton_iff.2 fun z hz ↦ ?_).antisymm
    (singleton_subset_iff.2 (mem_connectedComponentIn hx))
  -- Otherwise the component meets both open sets `U ∋ x` and `{x}ᶜ ∋ z`, which cover it, so it
  -- meets their intersection; but `U` meets `s` only at `x`.
  by_contra hzx
  obtain ⟨y, hy, hyU, hyx⟩ := isPreconnected_connectedComponentIn U {x}ᶜ hU isOpen_compl_singleton
    (fun y _ ↦ (eq_or_ne y x).elim (fun hyx ↦ Or.inl (hyx ▸ hxU)) Or.inr)
    ⟨x, mem_connectedComponentIn hx, hxU⟩ ⟨z, hz, hzx⟩
  exact hyx (hUx y hyU (connectedComponentIn_subset _ _ hy))

end TauCeti

/-- A function tending to a finite subset `S` of a Hausdorff space along a nontrivial filter `l`
tends to a single point of `S`, provided every set of `l` contains a set of `l` with preconnected
image. -/
theorem Filter.Tendsto.exists_mem_tendsto_nhds {β : Type*} [T2Space α] {f : β → α}
    {l : Filter β} [l.NeBot] {S : Set α} (hS : S.Finite) (hf : Tendsto f l (𝓝ˢ S))
    (hl : ∀ s ∈ l, ∃ t ∈ l, t ⊆ s ∧ IsPreconnected (f '' t)) : ∃ y ∈ S, Tendsto f l (𝓝 y) := by
  obtain ⟨U, hU, hdisj⟩ := hS.t2_separation
  have hdisj' : Pairwise (Disjoint on fun y : S ↦ U y) :=
    fun a b hab ↦ hdisj a.2 b.2 (Subtype.coe_injective.ne hab)
  -- Choose a set of `l` with preconnected image inside the union of the separating sets.
  have hV : (⋃ y : S, U y) ∈ 𝓝ˢ S :=
    (isOpen_iUnion fun y : S ↦ (hU y).2).mem_nhdsSet.2 fun y hy ↦
      mem_iUnion_of_mem ⟨y, hy⟩ (hU y).1
  obtain ⟨t, ht, hts, htc⟩ := hl _ (hf hV)
  obtain ⟨x, hx⟩ := l.nonempty_of_mem ht
  obtain ⟨y₀, hy₀⟩ := mem_iUnion.1 (hts hx)
  -- Its image lies in the single separating set it meets.
  have hsub : f '' t ⊆ U y₀ :=
    htc.subset_of_subset_iUnion (fun y : S ↦ (hU y).2) hdisj' (image_subset_iff.2 hts)
      ⟨f x, mem_image_of_mem f hx, hy₀⟩
  refine ⟨y₀, y₀.2, fun W hW ↦ ?_⟩
  -- Near `y₀` shrink its separating set to `W`; near the other points keep theirs.
  have hW' : (W ∩ U y₀ ∪ ⋃ y : {y : S // y ≠ y₀}, U y) ∈ 𝓝ˢ S := by
    refine mem_nhdsSet_iff_forall.2 fun y hy ↦ ?_
    by_cases hyy : (⟨y, hy⟩ : S) = y₀
    · subst hyy
      exact mem_of_superset (inter_mem hW ((hU _).2.mem_nhds (hU _).1)) subset_union_left
    · exact mem_of_superset ((hU y).2.mem_nhds (hU y).1)
        (subset_union_of_subset_right
          (subset_iUnion (fun y : {y : S // y ≠ y₀} ↦ U y) ⟨⟨y, hy⟩, hyy⟩) _)
  filter_upwards [hf hW', mem_map.2 (mem_of_superset ht (image_subset_iff.1 hsub))] with z hzW hz₀
  rcases hzW with hz | hz
  · exact hz.1
  · obtain ⟨y, hy⟩ := mem_iUnion.1 hz
    exact absurd (hdisj' y.2 |>.ne_of_mem hy hz₀) (by simp)

/-- **Preconnectedness pulls back along a continuous injection on a compact set.** If `f` is
continuous and injective on a compact `K` with values in a Hausdorff space, then `f '' K` is
preconnected exactly when `K` is. -/
theorem IsCompact.isPreconnected_image_iff_of_injOn {β : Type*} [TopologicalSpace β] [T2Space β]
    {f : α → β} {K : Set α} (hK : IsCompact K) (hf : ContinuousOn f K) (hinj : InjOn f K) :
    IsPreconnected (f '' K) ↔ IsPreconnected K := by
  -- On the subtype the restriction is a closed embedding, so it reflects preconnectedness.
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [isPreconnected_iff_preconnectedSpace (s := K), preconnectedSpace_iff_univ,
    ← (hf.domRestrict.isClosedEmbedding hinj.injective).isInducing.isPreconnected_image, image_univ,
    range_domRestrict]

/-- A preconnected set that meets `U` and misses its frontier lies in `U`. -/
theorem IsPreconnected.subset_of_disjoint_frontier {U s : Set α} (hs : IsPreconnected s)
    (hdisj : Disjoint s (frontier U)) (hmeet : (s ∩ U).Nonempty) : s ⊆ U := by
  obtain ⟨p, hps, hpU⟩ := hmeet
  -- A point of `U` off the frontier is interior, so `s` meets `interior U`.
  have hpint : p ∈ interior U := by
    by_contra hp
    exact hdisj.le_bot ⟨hps, subset_closure hpU, hp⟩
  have hdisj' : Disjoint s (frontier (interior U)) := hdisj.mono_right frontier_interior_subset
  refine (hs.subset_of_closure_inter_subset isOpen_interior ⟨p, hps, hpint⟩
    fun w ⟨hwcl, hws⟩ => ?_).trans interior_subset
  by_contra hwU
  have hwfr : w ∈ frontier (interior U) := by
    rw [isOpen_interior.frontier_eq]
    exact ⟨hwcl, hwU⟩
  exact hdisj'.le_bot ⟨hws, hwfr⟩

namespace TauCeti

/-- **Chains of overlaps in a connected open cover.** If the union of the open sets `V i`, `i ∈ t`,
is preconnected, every nonempty `V j` is joined to a nonempty piece `V i₀` by a chain of pairwise
overlapping pieces. -/
theorem reflTransGen_inter_nonempty_of_isOpen_cover {t : Set ι} {V : ι → Set α}
    (hU : IsPreconnected (⋃ i ∈ t, V i)) (hV : ∀ i ∈ t, IsOpen (V i))
    {i₀ : ι} (hi₀ : i₀ ∈ t) (hVi₀ : (V i₀).Nonempty) {j : ι} (hj : j ∈ t)
    (hVj : (V j).Nonempty) :
    Relation.ReflTransGen (fun i j ↦ i ∈ t ∧ j ∈ t ∧ (V i ∩ V j).Nonempty) i₀ j := by
  have hU' : IsPreconnected (⋃ k : t, V k) := by
    convert hU using 1
    ext
    simp
  exact (hU'.transGen_of_iUnion (fun k ↦ hV k k.2) ⟨i₀, hi₀⟩ ⟨j, hj⟩
    hVi₀ hVj).to_reflTransGen.lift Subtype.val (fun k l hkl ↦ ⟨k.2, l.2, hkl⟩)

end TauCeti
