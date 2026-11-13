/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Basic

/-!
# Shrinking a neighbourhood across finitely many sheets

For a map `q : Y → X` and finitely many open sets `S i` of `Y` (sheets), each mapped injectively
onto a common open set `U` of `X` and with the subspace topology from `q`, choose a point `y i`
of each sheet over `x` and an open neighbourhood `V i` of it. Then `U` shrinks to an open
`W ∋ x` such that every point of `W` lifts into each `S i ∩ V i`, and every point of a sheet
`S i` over `W` lies in `V i`. No covering-space hypothesis is needed.

## Main results

* `TauCeti.exists_isOpen_lift_mem_of_finite_sheets`: the finite shrinking of a base neighbourhood
  across sheets.
-/

public section

namespace TauCeti

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Finitely many sheets `S i` of `q` over `U ∋ x`, each containing a point `y i` over `x` and
an open neighbourhood `V i` of it: `U` shrinks to an open `W ∋ x` such that every point of
`S i` over `W` lies in `V i`, and every point of `W` is lifted into `S i ∩ V i`. -/
theorem exists_isOpen_lift_mem_of_finite_sheets {q : Y → X} {x : X} {U : Set X} {I : Type*}
    [Finite I] (hxU : x ∈ U) (hU : IsOpen U) {S V : I → Set Y} {y : I → Y}
    (hSo : ∀ i, IsOpen (S i)) (hSi : ∀ i, (S i).InjOn q) (hSim : ∀ i, q '' S i = U)
    (hSiff : ∀ i, ∀ W ⊆ U, IsOpen W ↔ IsOpen (q ⁻¹' W ∩ S i)) (hV : ∀ i, IsOpen (V i))
    (hyS : ∀ i, y i ∈ S i) (hyV : ∀ i, y i ∈ V i) (hyx : ∀ i, q (y i) = x) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ (∀ i, ∀ w ∈ W, ∃ z ∈ S i ∩ V i, q z = w) ∧
      ∀ i, ∀ z ∈ S i, q z ∈ W → z ∈ V i := by
  let W := U ∩ ⋂ i, q '' (S i ∩ V i)
  have hWo : IsOpen W := hU.inter <| isOpen_iInter_of_finite fun i ↦ by
    rw [hSiff i _ (hSim i ▸ image_mono inter_subset_left),
      (hSi i).preimage_image_inter inter_subset_left]
    exact (hSo i).inter (hV i)
  refine ⟨W, hWo, ⟨hxU, mem_iInter.mpr fun i ↦ ⟨y i, ⟨hyS i, hyV i⟩, hyx i⟩⟩,
    inter_subset_left, fun i w hw ↦ mem_iInter.mp hw.2 i, fun i z hz hw ↦ ?_⟩
  obtain ⟨z', ⟨hz'S, hz'V⟩, hz'⟩ := mem_iInter.mp hw.2 i
  rwa [← hSi i hz'S hz hz']

end TauCeti
