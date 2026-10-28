/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Preconnected sets covered by disjoint open sets

A preconnected set covered by a family of pairwise disjoint open sets lies in each member of the
family that it meets. This is the form in which connectedness is used to show that a region
contained in a union of disjoint open cells lies in a single cell.

The same principle selects a limit: a function which tends to a finite subset of a Hausdorff
space along a filter in which arbitrarily small sets have preconnected images tends to a single
point of that subset (`Filter.Tendsto.exists_mem_tendsto_nhds`). For instance, near a point
whose punctured neighbourhoods are connected, a continuous function approaching a finite set
chooses one of its points.
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
