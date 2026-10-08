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
# Maps and generic points for the constructible topology

The constructible topology refines the given topology on a prespectral space. Spectral maps
are continuous for the constructible topologies, and every generic point of the closure of a
subset lies in its constructible closure. These facts let pro-constructible subspaces inherit
compactness and quasi-sobriety under their respective ambient hypotheses.

## Main results

* `IsOpen.isOpen_constructibleTopology`: an open subset of a prespectral space is open for
  the constructible topology.
* `TauCeti.continuous_ofTopology_withConstructibleTopology`: the map from the constructible
  topology to the given topology of a prespectral space is continuous.
* `IsSpectralMap.continuous_constructibleTopology`: a spectral map is continuous for the
  constructible topologies.
* `IsGenericPoint.mem_closure_constructibleTopology`: a generic point of the closure of a
  subset lies in its constructible closure, in any topological space.

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

/-- Every generic point of the closure of a subset lies in its closure for the constructible
topology. -/
theorem IsGenericPoint.mem_closure_constructibleTopology {s : Set X} {η : X}
    (hη : IsGenericPoint η (closure s)) : η ∈ closure[constructibleTopology X] s := by
  -- A constructible basic neighborhood is a finite intersection of subbasic sets. The closed
  -- factors contain all of `closure s`; the intersection of the open factors must meet `s`.
  have hb := @isTopologicalBasis_of_subbasis X (constructibleTopology X)
    (constructibleTopologySubbasis X) rfl
  refine (@IsTopologicalBasis.mem_closure_iff X (constructibleTopology X) _ hb s η).2 ?_
  rintro _ ⟨F, ⟨hFfin, hFsub⟩, rfl⟩ hηF
  let O := {U ∈ F | IsOpen U}
  have hOfin : O.Finite := hFfin.subset fun _ hU ↦ hU.1
  have hOopen : IsOpen (⋂₀ O) := hOfin.isOpen_sInter fun _ hU ↦ hU.2
  have hηO : η ∈ ⋂₀ O := mem_sInter.2 fun U hU ↦ mem_sInter.1 hηF U hU.1
  obtain ⟨x, hxO, hxs⟩ := mem_closure_iff.1 hη.mem _ hOopen hηO
  refine ⟨x, mem_sInter.2 fun U hUF ↦ ?_, hxs⟩
  obtain ⟨hUopen, _⟩ | ⟨hUclosed, _⟩ := hFsub hUF
  · exact mem_sInter.1 hxO U ⟨hUF, hUopen⟩
  · exact (hη.mem_closed_set_iff hUclosed).1 (mem_sInter.1 hηF U hUF)
      (subset_closure hxs)
