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
whole graph, `LinearPMap.HasCore.graph_subset_of_isClosed`. For a closed partial map
this characterises cores: a submodule of its domain is a core exactly when the closure of
the graph of the restriction contains the whole graph,
`LinearPMap.IsClosed.hasCore_iff_graph_subset_closure`.

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
  have h := hA.mem_of_tendsto (hlim.prodMk_nhds hAlim)
    (.of_forall fun i => A.mem_graph ⟨u i, hu i⟩)
  exact ⟨mem_domain_of_mem_graph h, ((image_iff _).2 h).symm⟩

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

/-- A submodule `S` of the domain of a closed partial map `A` is a core for `A` if and only if the
graph of `A` lies in the closure of the graph of the restriction of `A` to `S`. -/
theorem IsClosed.hasCore_iff_graph_subset_closure {A : E →ₗ.[R] F} (hA : A.IsClosed)
    {S : Submodule R E} (hS : S ≤ A.domain) :
    A.HasCore S ↔
      (A.graph : Set (E × F)) ⊆ _root_.closure ((A.domRestrict S).graph : Set (E × F)) := by
  refine ⟨fun hS' => hS'.graph_subset_of_isClosed isClosed_closure subset_closure, fun h => ?_⟩
  have hT : (A.domRestrict S).IsClosable := hA.isClosable.leIsClosable domRestrict_le
  refine ⟨hS, eq_of_eq_graph ?_⟩
  rw [← hT.graph_closure_eq_closure_graph]
  refine le_antisymm (Submodule.topologicalClosure_minimal _ (le_graph_of_le domRestrict_le) hA) ?_
  rwa [← SetLike.coe_subset_coe, Submodule.topologicalClosure_coe]

end LinearPMap
