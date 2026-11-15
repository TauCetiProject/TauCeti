/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Order.Disjointed

/-!
# Disjoint measurable covers subordinate to neighbourhoods

In a hereditarily Lindelöf space, if every point `x` of a nonempty set `S` has a measurable
neighbourhood `N x`, then countably many of the `N x` already cover `S`, and making them disjoint
gives a countable cover of `S` by pairwise disjoint measurable sets, each contained in one of the
chosen neighbourhoods (`TauCeti.exists_disjoint_measurableSet_cover_of_mem_nhds`). This is the
usual way to pass from a statement proved near every point of a set to the whole set, when the
statement is additive over disjoint measurable pieces.
-/

public section

open Function Set
open scoped Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [HereditarilyLindelofSpace α] [MeasurableSpace α]

/-- In a hereditarily Lindelöf space, if every point of a nonempty set `S` has a measurable
neighbourhood `N x`, then `S` is covered by countably many pairwise disjoint measurable sets,
each contained in one of these neighbourhoods. -/
theorem exists_disjoint_measurableSet_cover_of_mem_nhds {S : Set α} (hS : S.Nonempty)
    (N : α → Set α) (hN : ∀ x ∈ S, N x ∈ 𝓝 x) (hNm : ∀ x ∈ S, MeasurableSet (N x)) :
    ∃ D : ℕ → Set α, (∀ n, MeasurableSet (D n)) ∧ Pairwise (Disjoint on D) ∧
      S ⊆ ⋃ n, D n ∧ ∀ n, ∃ x ∈ S, D n ⊆ N x := by
  have : Nonempty S := hS.to_subtype
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover
    (fun x : S ↦ interior (N x)) (fun _ ↦ isOpen_interior)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hN x hx)⟩
  refine ⟨disjointed fun n ↦ N (f n), MeasurableSet.disjointed fun n ↦ hNm _ (f n).2,
    disjoint_disjointed _, ?_, fun n ↦ ⟨f n, (f n).2, disjointed_subset _ n⟩⟩
  rw [iUnion_disjointed]
  exact hf.trans (iUnion_mono fun n ↦ interior_subset)

end TauCeti
