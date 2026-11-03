/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closed-graph limits for partial linear maps

Mathlib's `LinearPMap.HasCore` is the canonical abstraction for graph cores:
`A.HasCore S` means that restricting `A` to `S` and taking its closure
recovers `A`. No second graph-core predicate is needed.

A closed graph contains the limit of a domain-valued net whenever the vectors
and their images both converge along a nontrivial filter. Dually, a closed set
containing the graph of the restriction of a partial map to a core contains its
whole graph, `LinearPMap.HasCore.graph_subset_of_isClosed`. Conversely, a submodule of the
domain of a closed partial map is a core once the closure of the graph of the restriction
contains the whole graph, `LinearPMap.HasCore.of_graph_subset_closure`.

## Provenance

Adapted from the graph-limit argument in the Apache-2.0 DKPS formalization
(`DavisKahan/Sources/DavisKahan1970/SineTheta/CommonCore.lean`, Kitware, Inc.),
formerly phrased for the project's bundled closed-operator representation.
-/

public section

namespace LinearPMap

open Filter Topology

variable {R E F : Type*} [CommRing R]
variable [AddCommGroup E] [AddCommGroup F] [Module R E] [Module R F]
variable [TopologicalSpace E] [TopologicalSpace F]

/-- A closed partial map contains the limit of a domain-valued net whose images
converge; its value at the limit is the limit of the images. -/
theorem IsClosed.mem_domain_of_tendsto
    {A : E →ₗ.[R] F} (hA : A.IsClosed)
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → E} {x : E} {y : F}
    (hu : ∀ i, u i ∈ A.domain)
    (hlim : Tendsto u l (𝓝 x))
    (hAlim : Tendsto (fun i => A ⟨u i, hu i⟩) l (𝓝 y)) :
    ∃ h : x ∈ A.domain, A ⟨x, h⟩ = y := by
  have hmem : ∀ i, (u i, A ⟨u i, hu i⟩) ∈ (A.graph : Set (E × F)) :=
    fun i => A.mem_graph ⟨u i, hu i⟩
  have hpair : Tendsto (fun i => (u i, A ⟨u i, hu i⟩)) l (𝓝 (x, y)) :=
    hlim.prodMk_nhds hAlim
  have hlimmem : (x, y) ∈ (A.graph : Set (E × F)) :=
    hA.mem_of_tendsto hpair (Eventually.of_forall hmem)
  obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff A).1 hlimmem
  dsimp only at hv1 hv2
  have hxmem : x ∈ A.domain := hv1 ▸ v.property
  refine ⟨hxmem, ?_⟩
  have hveq : (⟨x, hxmem⟩ : A.domain) = v := Subtype.ext hv1.symm
  rw [hveq, hv2]

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- A closed set containing the graph of the restriction of `A` to a core `S` contains the whole
graph of `A`, since that graph is the closure of the graph of the restriction. -/
theorem HasCore.graph_subset_of_isClosed {A : E →ₗ.[R] F} {S : Submodule R E}
    (hS : A.HasCore S) {s : Set (E × F)} (hs : _root_.IsClosed s)
    (h : ((A.domRestrict S).graph : Set (E × F)) ⊆ s) : (A.graph : Set (E × F)) ⊆ s := by
  rw [← hS.closure_eq]
  by_cases hT : (A.domRestrict S).IsClosable
  · rw [← hT.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe]
    exact closure_minimal h hs
  · rwa [closure_def' hT]

/-- A submodule `S` of the domain of a closed partial map `A` is a core for `A` as soon as the graph
of `A` lies in the closure of the graph of the restriction of `A` to `S`. -/
theorem HasCore.of_graph_subset_closure {A : E →ₗ.[R] F} (hA : A.IsClosed) {S : Submodule R E}
    (hS : S ≤ A.domain)
    (h : (A.graph : Set (E × F)) ⊆ _root_.closure ((A.domRestrict S).graph : Set (E × F))) :
    A.HasCore S := by
  have hT : (A.domRestrict S).IsClosable := hA.isClosable.leIsClosable domRestrict_le
  refine ⟨hS, eq_of_eq_graph ?_⟩
  rw [← hT.graph_closure_eq_closure_graph]
  refine le_antisymm (Submodule.topologicalClosure_minimal _ (le_graph_of_le domRestrict_le) hA) ?_
  rwa [← SetLike.coe_subset_coe, Submodule.topologicalClosure_coe]

end LinearPMap
