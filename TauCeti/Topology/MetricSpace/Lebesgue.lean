/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The Lebesgue number lemma for neighbourhood covers

Mathlib's `lebesgue_number_lemma_of_metric` is stated for a cover of a compact set by open sets.
This file records the variant for a family of sets such that every point of the compact set has
some member of the family as a neighbourhood, as happens for the preimages of such a cover under
a continuous map. It also records the consequence for an injective continuous map `f` from a
compact space to a metric space: points with close images lie in a common member of any open
cover of the domain.

## Main declarations

* `TauCeti.lebesgue_number_lemma_of_metric_of_mem_nhds`: a Lebesgue number for a family of sets
  one of which is a neighbourhood of each point of a compact set.
* `TauCeti.exists_pos_forall_dist_lt_exists_mem`: for an injective continuous map from a compact
  space to a metric space and an open cover of the domain, a positive `m` such that any two points
  whose images are at distance less than `m` lie in a common member of the cover.
-/

public section

open Function Set Metric Topology

namespace TauCeti

/-- A Lebesgue number for a family of sets `c` such that every point of the compact set `s` has
some `c i` as a neighbourhood: there is `δ > 0` such that the ball of radius `δ` around any point
of `s` is contained in some `c i`. -/
theorem lebesgue_number_lemma_of_metric_of_mem_nhds {α : Type*} {ι : Sort*} [PseudoMetricSpace α]
    {s : Set α} {c : ι → Set α} (hs : IsCompact s) (hc : ∀ x ∈ s, ∃ i, c i ∈ 𝓝 x) :
    ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric hs (c := fun i ↦ interior (c i))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 <| (hc x hx).imp fun _ ↦ mem_interior_iff_mem_nhds.2
  exact ⟨δ, hδ, fun x hx ↦ (h x hx).imp fun _ hi ↦ hi.trans interior_subset⟩

/-- For an injective continuous map `f` from a compact space to a metric space, and an open cover
`W` of the domain, there is `m > 0` such that any two points whose images are at distance less
than `m` lie in a common member of the cover. -/
theorem exists_pos_forall_dist_lt_exists_mem {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] {f : X → Y} (hf : Continuous f) (hinj : Injective f) {ι : Sort*}
    {W : ι → Set X} (hWo : ∀ i, IsOpen (W i)) (ht : univ ⊆ ⋃ i, W i) :
    ∃ m > 0, ∀ y z : X, dist (f y) (f z) < m → ∃ i, y ∈ W i ∧ z ∈ W i := by
  have hemb := hf.isClosedEmbedding hinj
  choose U hUo hU using fun i => hemb.isInducing.isOpen_iff.mp (hWo i)
  obtain ⟨m, hm, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_range hf) hUo
    (c := U) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (ht (mem_univ y))
      exact mem_iUnion.mpr ⟨i, by rw [← mem_preimage, hU]; exact hi⟩)
  refine ⟨m, hm, fun y z hyz => ?_⟩
  obtain ⟨i, hi⟩ := hball (f y) ⟨y, rfl⟩
  refine ⟨i, ?_, ?_⟩
  · rw [← hU i]
    exact hi (mem_ball_self hm)
  · rw [← hU i]
    exact hi (by rwa [mem_ball, dist_comm])

end TauCeti
