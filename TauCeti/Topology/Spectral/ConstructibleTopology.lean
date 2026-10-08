/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Prespectral
import Mathlib.Topology.WithTopology

/-!
# Maps and inseparable points for the constructible topology

The constructible topology refines the given topology on a prespectral space. Spectral maps
are continuous for the constructible topologies, and topologically indistinguishable points
remain indistinguishable in the constructible topology. These facts let pro-constructible
subspaces inherit compactness and quasi-sobriety without a separation hypothesis.

## Main results

* `IsOpen.isOpen_constructibleTopology`: an open subset of a prespectral space is open for
  the constructible topology.
* `TauCeti.continuous_ofTopology_withConstructibleTopology`: the map from the constructible
  topology to the given topology of a prespectral space is continuous.
* `IsSpectralMap.continuous_constructibleTopology`: a spectral map is continuous for the
  constructible topologies.
* `Inseparable.constructibleTopology`: indistinguishable points remain indistinguishable
  for the constructible topology.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §3.
-/

public section

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### The constructible topology refines the given topology -/

/-- On a prespectral space every open subset is open for the constructible topology: an open set
is a union of quasi-compact opens, and those belong to the defining subbasis. -/
theorem IsOpen.isOpen_constructibleTopology [PrespectralSpace X] {s : Set X} (hs : IsOpen s) :
    IsOpen[constructibleTopology X] s := by
  rw [(PrespectralSpace.isTopologicalBasis (X := X)).open_eq_sUnion' hs]
  refine @isOpen_sUnion X (constructibleTopology X) _ ?_
  rintro U ⟨⟨hUo, hUc⟩, -⟩
  exact hUc.isOpen_constructibleTopology_of_isOpen hUo

variable (X) in
/-- On a prespectral space the identity map from the constructible topology to the given topology
is continuous. -/
theorem TauCeti.continuous_ofTopology_withConstructibleTopology [PrespectralSpace X] :
    Continuous (WithTopology.ofTopology : WithConstructibleTopology X → X) :=
  continuous_def.2 fun _ hs ↦
    WithConstructibleTopology.isOpen_iff.2 hs.isOpen_constructibleTopology

/-- A spectral map is continuous for the constructible topologies: it pulls the defining subbasis
back into itself. -/
theorem IsSpectralMap.continuous_constructibleTopology {f : X → Y} (hf : IsSpectralMap f) :
    Continuous[constructibleTopology X, constructibleTopology Y] f := by
  refine continuous_generateFrom_iff.2 fun U hU ↦ ?_
  obtain ⟨hUo, hUc⟩ | ⟨hUcl, hUcc⟩ := hU
  · exact (hUc.preimage_of_isOpen hf hUo).isOpen_constructibleTopology_of_isOpen
      (hUo.preimage hf.continuous)
  · refine IsCompact.isOpen_constructibleTopology_of_isClosed ?_ (hUcl.preimage hf.continuous)
    rw [← Set.preimage_compl]
    exact hUcc.preimage_of_isOpen hf hUcl.isOpen_compl

/-- Topologically indistinguishable points remain indistinguishable for the constructible
topology: every subbasic set is an open set or the complement of an open set. -/
theorem Inseparable.constructibleTopology {x y : X} (h : Inseparable x y) :
    @Inseparable X (constructibleTopology X) x y := by
  have hi : {s : Set X | x ∈ s ∧ s ∈ constructibleTopologySubbasis X} =
      {s : Set X | y ∈ s ∧ s ∈ constructibleTopologySubbasis X} := by
    ext s
    apply and_congr_left
    rintro (⟨ho, _⟩ | ⟨hc, _⟩)
    · exact h.mem_open_iff ho
    · exact h.mem_closed_iff hc
  exact (@inseparable_def X (_root_.constructibleTopology X) x y).2 <| by
    simp only [nhds_generateFrom, hi]
