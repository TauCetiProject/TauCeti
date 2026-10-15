/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The Lebesgue number lemma for neighbourhood covers

Mathlib's `lebesgue_number_lemma_of_metric` is stated for a cover of a compact set by open sets.
This file records the variant for a family of sets such that every point of the compact set has
some member of the family as a neighbourhood, as happens for the preimages of such a cover under
a continuous map.

## Main declarations

* `TauCeti.lebesgue_number_lemma_of_metric_of_mem_nhds`: a Lebesgue number for a family of sets
  one of which is a neighbourhood of each point of a compact set.
-/

public section

open Set Metric Topology

namespace TauCeti

/-- A Lebesgue number for a family of sets `c` such that every point of the compact set `s` has
some `c i` as a neighbourhood: there is `δ > 0` such that the ball of radius `δ` around any point
of `s` is contained in some `c i`. -/
theorem lebesgue_number_lemma_of_metric_of_mem_nhds {α ι : Type*} [PseudoMetricSpace α]
    {s : Set α} {c : ι → Set α} (hs : IsCompact s) (hc : ∀ x ∈ s, ∃ i, c i ∈ 𝓝 x) :
    ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric hs (c := fun i ↦ interior (c i))
    (fun _ ↦ isOpen_interior) fun x hx ↦ by
      obtain ⟨i, hi⟩ := hc x hx
      exact mem_iUnion.2 ⟨i, mem_interior_iff_mem_nhds.2 hi⟩
  exact ⟨δ, hδ, fun x hx ↦ (h x hx).imp fun _ hi ↦ hi.trans interior_subset⟩

end TauCeti
