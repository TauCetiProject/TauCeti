/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Connectivity.CutCapacity
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Isomorphism
public import TauCeti.Combinatorics.Graph.Simple

/-!
# Isomorphism invariance of multigraph connectivity

A multigraph isomorphism transports subsets of the actual vertices and edges by its two
underlying equivalences. This transport sends an edge cut to the edge cut of the transported
vertex side, and consequently preserves edge cuts, bridges, and bonds. It also preserves the
absence of cycles, hence multigraph forests. For finite edge sets, it preserves weighted cut
capacities and their aggregation by unordered pairs of vertices.

Isomorphisms also preserve local and global edge- and vertex-connectivity and their numerical
invariants. The edge statements retain edge identities, including loops and parallel edges;
the vertex statements use the induced isomorphism of underlying simple graphs. All endpoints
are actual vertices. No finiteness is needed, so the results include infinite connectivity
and the empty-graph conventions.

An isomorphism also induces an equivalence of connected-component subgraphs, sending each
component to the component with the transported vertices and edges. Hence it preserves
connectedness and the component count.

The set transport is stated on the ambient vertex and edge types because Mathlib's
`Graph.edgeCut`, `Graph.IsEdgeCut`, and `Graph.IsBond` use ambient sets. Elements outside the
actual carrier are discarded. On subsets of the actual carrier, transport along the inverse
isomorphism is an exact inverse.
-/

public section

open Finset Set

universe u v u' v' w

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {K : Type w}
variable {G : Graph α β} {H : Graph α' β'}

namespace Iso

/-- An edge crosses a transported vertex side exactly when its inverse image crosses the original
side. -/
theorem edgeEquiv_mem_edgeCut_mapVertexSet_iff (f : Iso G H) (S : Set α)
    (e : G.edgeSet) :
    (f.edgeEquiv e : β') ∈ H.edgeCut (f.mapVertexSet S) ↔ (e : β) ∈ G.edgeCut S := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
  rw [(f.map_isLink hxy).mem_edgeCut_iff, hxy.mem_edgeCut_iff]
  simp

/-! ### Cut capacities -/

/-- A graph isomorphism preserves the capacity of every cut once the edge capacities are
relabelled along it. -/
theorem edgeCutCapacity_map [Fintype E(G)] [Fintype E(H)] [AddCommMonoid K] (f : Iso G H)
    (c : E(G) → K) (S : Finset V(G)) :
    H.edgeCutCapacity (c ∘ f.edgeEquiv.symm) (S.map f.vertexEquiv.toEmbedding) =
      G.edgeCutCapacity c S := by
  classical
  rw [edgeCutCapacity_def, edgeCutCapacity_def, coe_map, Equiv.coe_toEmbedding,
    ← mapVertexSet_image_val]
  exact (Fintype.sum_equiv f.edgeEquiv _ _ fun e ↦ by
    simp [f.edgeEquiv_mem_edgeCut_mapVertexSet_iff]).symm

/-- A graph isomorphism preserves the aggregated capacity of every unordered pair of actual
vertices once the edge capacities are relabelled along it. -/
theorem pairCapacity_map [Fintype E(G)] [Fintype E(H)] [AddCommMonoid K] (f : Iso G H)
    (c : E(G) → K) (p : Sym2 V(G)) :
    H.pairCapacity (c ∘ f.edgeEquiv.symm) (p.map f.vertexEquiv) = G.pairCapacity c p := by
  classical
  rw [pairCapacity_def, pairCapacity_def]
  exact (Fintype.sum_equiv f.edgeEquiv _ _ fun e ↦ by
    simp [Sym2.isDiag_map f.vertexEquiv.injective,
      (Sym2.map.injective f.vertexEquiv.injective).eq_iff]).symm

/-- Transporting an edge cut gives the edge cut of the transported vertex side. -/
theorem mapEdgeSet_edgeCut (f : Iso G H) (S : Set α) :
    f.mapEdgeSet (G.edgeCut S) = H.edgeCut (f.mapVertexSet S) := by
  ext e
  by_cases he : e ∈ E(H)
  · let e' : H.edgeSet := ⟨e, he⟩
    have hcut := f.edgeEquiv_mem_edgeCut_mapVertexSet_iff S (f.edgeEquiv.symm e')
    have hmem := f.mem_mapEdgeSet_iff (G.edgeCut S) e'
    simpa [e'] using hmem.trans hcut.symm
  · have hleft : e ∉ f.mapEdgeSet (G.edgeCut S) := fun h ↦
      he (f.mapEdgeSet_subset_edgeSet _ h)
    have hright : e ∉ H.edgeCut (f.mapVertexSet S) := fun h ↦
      he (H.edgeCut_subset_edgeSet h)
    exact iff_of_false hleft hright

/-- A graph isomorphism sends edge cuts to edge cuts. -/
theorem map_isEdgeCut (f : Iso G H) {F : Set β} (hF : G.IsEdgeCut F) :
    H.IsEdgeCut (f.mapEdgeSet F) := by
  rw [isEdgeCut_iff] at hF ⊢
  obtain ⟨S, rfl⟩ := hF
  exact ⟨f.mapVertexSet S, (f.mapEdgeSet_edgeCut S).symm⟩

/-- Edge-cut status is invariant under graph isomorphism for a set of actual edges. -/
theorem isEdgeCut_mapEdgeSet_iff (f : Iso G H) {F : Set β} (hF : F ⊆ E(G)) :
    H.IsEdgeCut (f.mapEdgeSet F) ↔ G.IsEdgeCut F := by
  refine ⟨fun h ↦ ?_, f.map_isEdgeCut⟩
  have h' := f.symm.map_isEdgeCut h
  rwa [f.symm_mapEdgeSet_mapEdgeSet hF] at h'

/-- Bridge status is invariant under graph isomorphism. -/
theorem isBridge_edgeEquiv_iff (f : Iso G H) (e : G.edgeSet) :
    H.IsBridge (f.edgeEquiv e) ↔ G.IsBridge e := by
  have hcut := f.isEdgeCut_mapEdgeSet_iff (singleton_subset_iff.mpr e.property)
  simpa only [Graph.IsBridge, f.mapEdgeSet_singleton e] using hcut

/-- A graph isomorphism sends bonds to bonds. -/
theorem map_isBond (f : Iso G H) {B : Set β} (hB : G.IsBond B) :
    H.IsBond (f.mapEdgeSet B) := by
  refine ⟨⟨f.map_isEdgeCut hB.isEdgeCut,
    (f.mapEdgeSet_nonempty_iff hB.subset).2 hB.nonempty⟩, ?_⟩
  intro C hC hCB
  have hCE : C ⊆ E(H) := hC.1.subset_edgeSet
  have hpreCut : G.IsEdgeCut (f.symm.mapEdgeSet C) := f.symm.map_isEdgeCut hC.1
  have hpreNonempty : (f.symm.mapEdgeSet C).Nonempty :=
    (f.symm.mapEdgeSet_nonempty_iff hCE).2 hC.2
  have hpreB : f.symm.mapEdgeSet C ⊆ B := by
    have h := f.symm.mapEdgeSet_mono hCB
    rwa [f.symm_mapEdgeSet_mapEdgeSet hB.subset] at h
  have hBpre : B ⊆ f.symm.mapEdgeSet C := hB.2 ⟨hpreCut, hpreNonempty⟩ hpreB
  have hmap := f.mapEdgeSet_mono hBpre
  have hround := f.symm.symm_mapEdgeSet_mapEdgeSet hCE
  rw [symm_symm] at hround
  exact hmap.trans_eq hround

/-- Bond status is invariant under graph isomorphism. -/
theorem isBond_mapEdgeSet_iff (f : Iso G H) {B : Set β} (hB : B ⊆ E(G)) :
    H.IsBond (f.mapEdgeSet B) ↔ G.IsBond B := by
  refine ⟨fun h ↦ ?_, f.map_isBond⟩
  have h' := f.symm.map_isBond h
  rwa [f.symm_mapEdgeSet_mapEdgeSet hB] at h'

/-- The set of bridges is transported pointwise by a graph isomorphism. -/
theorem mapEdgeSet_bridgeSet (f : Iso G H) : f.mapEdgeSet G.bridgeSet = H.bridgeSet := by
  ext e
  by_cases he : e ∈ E(H)
  · let e' : H.edgeSet := ⟨e, he⟩
    have hmem := f.mem_mapEdgeSet_iff G.bridgeSet e'
    calc
      e ∈ f.mapEdgeSet G.bridgeSet ↔
          (f.edgeEquiv.symm e' : β) ∈ G.bridgeSet := by simpa [e'] using hmem
      _ ↔ G.IsBridge (f.edgeEquiv.symm e') := mem_bridgeSet
      _ ↔ H.IsBridge e := by simpa [e'] using
        (f.isBridge_edgeEquiv_iff (f.edgeEquiv.symm e')).symm
      _ ↔ e ∈ H.bridgeSet := mem_bridgeSet.symm
  · have hleft : e ∉ f.mapEdgeSet G.bridgeSet := fun h ↦
      he (f.mapEdgeSet_subset_edgeSet _ h)
    have hright : e ∉ H.bridgeSet := fun h ↦ he (mem_bridgeSet.mp h).mem_edgeSet
    exact iff_of_false hleft hright

/-- Being a forest is invariant under graph isomorphism. -/
theorem isForest_iff (f : Iso G H) : H.IsForest ↔ G.IsForest := by
  rw [H.isForest_iff_forall_isBridge, G.isForest_iff_forall_isBridge]
  constructor
  · intro hH e he
    exact (f.isBridge_edgeEquiv_iff ⟨e, he⟩).mp (hH (f.edgeEquiv ⟨e, he⟩).property)
  · intro hG e he
    let e' : H.edgeSet := ⟨e, he⟩
    simpa [e'] using (f.isBridge_edgeEquiv_iff (f.edgeEquiv.symm e')).mpr
      (hG (f.edgeEquiv.symm e').property)

/-- Edge reachability at every natural threshold is invariant under multigraph isomorphism. -/
@[simp]
theorem isEdgeReachable_iff (f : Iso G H) (k : ℕ) (x y : V(G)) :
    H.IsEdgeReachable k (f.vertexEquiv x) (f.vertexEquiv y) ↔ G.IsEdgeReachable k x y := by
  rw [isEdgeReachable_iff_forall_subset_edgeSet, isEdgeReachable_iff_forall_subset_edgeSet]
  constructor
  · intro h F hF hcard
    exact (f.reachable_deleteEdges_mapEdgeSet_iff F x y).mp
      (h (f.mapEdgeSet_subset_edgeSet F) (by simpa only [f.encard_mapEdgeSet hF] using hcard))
  · intro h F hF hcard
    have hr := h (f.symm.mapEdgeSet_subset_edgeSet F)
      (by simpa only [f.symm.encard_mapEdgeSet hF] using hcard)
    have ht := (f.reachable_deleteEdges_mapEdgeSet_iff (f.symm.mapEdgeSet F) x y).mpr hr
    have hround := f.symm.symm_mapEdgeSet_mapEdgeSet hF
    rw [symm_symm] at hround
    rwa [hround] at ht

/-- Global edge connectivity is invariant under multigraph isomorphism, including for empty
actual vertex sets. -/
theorem isEdgeConnected_iff (f : Iso G H) (k : ℕ) :
    H.IsEdgeConnected k ↔ G.IsEdgeConnected k := by
  simp only [isEdgeConnected_def]
  constructor
  · intro h x hx y hy
    exact (f.isEdgeReachable_iff k ⟨x, hx⟩ ⟨y, hy⟩).mp
      (h (f.vertexEquiv ⟨x, hx⟩).property (f.vertexEquiv ⟨y, hy⟩).property)
  · intro h x hx y hy
    have hr := (f.isEdgeReachable_iff k (f.vertexEquiv.symm ⟨x, hx⟩)
      (f.vertexEquiv.symm ⟨y, hy⟩)).mpr
        (h (f.vertexEquiv.symm ⟨x, hx⟩).property (f.vertexEquiv.symm ⟨y, hy⟩).property)
    simpa using hr

/-- Local numerical edge reachability is unchanged by a multigraph isomorphism. -/
@[simp]
theorem edgeReachability_eq (f : Iso G H) (x y : V(G)) :
    H.edgeReachability (f.vertexEquiv x) (f.vertexEquiv y) = G.edgeReachability x y := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  simp only [← isEdgeReachable_iff_le_edgeReachability, f.isEdgeReachable_iff]

/-- Numerical edge connectivity is unchanged by a multigraph isomorphism. -/
theorem edgeConnectivity_eq (f : Iso G H) : H.edgeConnectivity = G.edgeConnectivity := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  simp only [← isEdgeConnected_iff_le_edgeConnectivity, f.isEdgeConnected_iff]

/-- Local vertex reachability is invariant under multigraph isomorphism. -/
@[simp]
theorem isVertexReachable_iff (f : Iso G H) (k : ℕ) (x y : V(G)) :
    H.IsVertexReachable k (f.vertexEquiv x) (f.vertexEquiv y) ↔ G.IsVertexReachable k x y := by
  simpa only [toSimpleGraphIso_apply] using
    (f.toSimpleGraphIso.isVertexReachable_iff (k := (k : ℕ∞)) x y)

/-- Global vertex connectivity is invariant under multigraph isomorphism. -/
theorem isVertexConnected_iff (f : Iso G H) (k : ℕ) :
    H.IsVertexConnected k ↔ G.IsVertexConnected k :=
  f.toSimpleGraphIso.isVertexConnected_iff

/-- Numerical vertex connectivity is unchanged by a multigraph isomorphism, including on the
empty actual vertex set. -/
theorem vertexConnectivity_eq (f : Iso G H) : H.vertexConnectivity = G.vertexConnectivity :=
  f.toSimpleGraphIso.vertexConnectivity_eq

/-- A native multigraph cut vertex is carried to a native cut vertex by a multigraph
isomorphism. -/
@[simp]
theorem isCutVertex_vertexEquiv_iff (f : Iso G H) (x : V(G)) :
    H.IsCutVertex (f.vertexEquiv x) ↔ G.IsCutVertex x := by
  rw [H.isCutVertex_iff_toSimpleGraph_isCutVertex (f.vertexEquiv x).property,
    G.isCutVertex_iff_toSimpleGraph_isCutVertex x.property]
  simpa only [toSimpleGraphIso_apply] using
    (f.toSimpleGraphIso.isCutVertex_iff (v := x))

/-! ### Connected components -/

/-- Multigraph connectedness is invariant under isomorphism, including for empty actual vertex
sets. -/
theorem connected_iff (f : Iso G H) : H.Connected ↔ G.Connected := by
  rw [connected_iff_toSimpleGraph_connected, connected_iff_toSimpleGraph_connected]
  exact f.toSimpleGraphIso.connected_iff.symm

/-- A multigraph isomorphism induces an equivalence of connected-component subgraphs. -/
noncomputable def connectedComponentEquiv (f : Iso G H) :
    G.ConnectedComponent ≃ H.ConnectedComponent :=
  G.connectedComponentEquiv.trans
    (f.toSimpleGraphIso.connectedComponentEquiv.trans H.connectedComponentEquiv.symm)

/-- The component of an actual vertex is sent to the component of its image. -/
@[simp]
theorem connectedComponentEquiv_connectedComponentOf (f : Iso G H) {x : α} (hx : x ∈ V(G)) :
    f.connectedComponentEquiv (G.connectedComponentOf x hx) =
      H.connectedComponentOf (f.vertexEquiv ⟨x, hx⟩) (f.vertexEquiv ⟨x, hx⟩).property := by
  apply H.connectedComponentEquiv.injective
  simp [connectedComponentEquiv]

/-- An actual vertex lies in the transported component exactly when its preimage lies in the
original component. -/
@[simp]
theorem vertexEquiv_mem_vertexSet_connectedComponentEquiv_iff (f : Iso G H)
    (C : G.ConnectedComponent) (x : V(G)) :
    (f.vertexEquiv x : α') ∈ V((f.connectedComponentEquiv C).val) ↔ (x : α) ∈ V(C.val) := by
  obtain ⟨z, hz⟩ := C.property.nonempty
  rw [ConnectedComponent.eq_connectedComponentOf (C := C) hz,
    mem_vertexSet_connectedComponentOf_iff, connectedComponentEquiv_connectedComponentOf,
    mem_vertexSet_connectedComponentOf_iff]
  exact f.reachable_iff ⟨z, _⟩ x

/-- An actual edge lies in the transported component exactly when its preimage lies in the
original component. -/
@[simp]
theorem edgeEquiv_mem_edgeSet_connectedComponentEquiv_iff (f : Iso G H)
    (C : G.ConnectedComponent) (e : E(G)) :
    (f.edgeEquiv e : β') ∈ E((f.connectedComponentEquiv C).val) ↔ (e : β) ∈ E(C.val) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
  have hfxy := f.map_isLink hxy
  rw [Subtype.coe_eta] at hfxy
  exact (((f.connectedComponentEquiv C).property.isClosedSubgraph.mem_tfae_of_isLink hfxy).out
    3 1).trans ((f.vertexEquiv_mem_vertexSet_connectedComponentEquiv_iff C _).trans
      ((C.property.isClosedSubgraph.mem_tfae_of_isLink hxy).out 1 3))

/-- The vertices of a transported component are the transported vertices of the component. -/
theorem vertexSet_connectedComponentEquiv (f : Iso G H) (C : G.ConnectedComponent) :
    V((f.connectedComponentEquiv C).val) = f.mapVertexSet V(C.val) := by
  ext y
  by_cases hy : y ∈ V(H)
  · let y' : V(H) := ⟨y, hy⟩
    have h := f.vertexEquiv_mem_vertexSet_connectedComponentEquiv_iff C (f.vertexEquiv.symm y')
    rw [Equiv.apply_symm_apply] at h
    exact h.trans (f.mem_mapVertexSet_iff _ y').symm
  · exact iff_of_false (fun h ↦ hy ((f.connectedComponentEquiv C).property.le.vertexSet_mono h))
      fun h ↦ hy (f.mapVertexSet_subset_vertexSet _ h)

/-- The edges of a transported component are the transported edges of the component. -/
theorem edgeSet_connectedComponentEquiv (f : Iso G H) (C : G.ConnectedComponent) :
    E((f.connectedComponentEquiv C).val) = f.mapEdgeSet E(C.val) := by
  ext e
  by_cases he : e ∈ E(H)
  · let e' : E(H) := ⟨e, he⟩
    have h := f.edgeEquiv_mem_edgeSet_connectedComponentEquiv_iff C (f.edgeEquiv.symm e')
    rw [Equiv.apply_symm_apply] at h
    exact h.trans (f.mem_mapEdgeSet_iff _ e').symm
  · exact iff_of_false (fun h ↦ he ((f.connectedComponentEquiv C).property.le.edgeSet_mono h))
      fun h ↦ he (f.mapEdgeSet_subset_edgeSet _ h)

/-- The identity isomorphism induces the identity on connected components. -/
@[simp]
theorem connectedComponentEquiv_refl : (refl G).connectedComponentEquiv = Equiv.refl _ := by
  ext1 C
  simp [connectedComponentEquiv]

/-- The inverse isomorphism induces the inverse equivalence of connected components. -/
@[simp]
theorem connectedComponentEquiv_symm (f : Iso G H) :
    f.symm.connectedComponentEquiv = f.connectedComponentEquiv.symm := by
  ext1 C
  simp [connectedComponentEquiv]

/-- The inverse component equivalence sends the component of an actual vertex to the component of
its preimage. -/
@[simp]
theorem connectedComponentEquiv_symm_connectedComponentOf (f : Iso G H) {y : α'}
    (hy : y ∈ V(H)) :
    f.connectedComponentEquiv.symm (H.connectedComponentOf y hy) =
      G.connectedComponentOf (f.vertexEquiv.symm ⟨y, hy⟩)
        (f.vertexEquiv.symm ⟨y, hy⟩).property := by
  simpa using f.symm.connectedComponentEquiv_connectedComponentOf hy

/-- An actual vertex lies in the component pulled back along the isomorphism exactly when its
image lies in the original component. -/
@[simp]
theorem vertexEquiv_symm_mem_vertexSet_connectedComponentEquiv_symm_iff (f : Iso G H)
    (D : H.ConnectedComponent) (y : V(H)) :
    (f.vertexEquiv.symm y : α) ∈ V((f.connectedComponentEquiv.symm D).val) ↔
      (y : α') ∈ V(D.val) := by
  simpa using f.symm.vertexEquiv_mem_vertexSet_connectedComponentEquiv_iff D y

/-- An actual edge lies in the component pulled back along the isomorphism exactly when its image
lies in the original component. -/
@[simp]
theorem edgeEquiv_symm_mem_edgeSet_connectedComponentEquiv_symm_iff (f : Iso G H)
    (D : H.ConnectedComponent) (e : E(H)) :
    (f.edgeEquiv.symm e : β) ∈ E((f.connectedComponentEquiv.symm D).val) ↔
      (e : β') ∈ E(D.val) := by
  simpa using f.symm.edgeEquiv_mem_edgeSet_connectedComponentEquiv_iff D e

/-- Composing isomorphisms composes their equivalences of connected components. -/
@[simp]
theorem connectedComponentEquiv_trans {α'' β'' : Type*} {K : Graph α'' β''} (f : Iso G H)
    (g : Iso H K) :
    (f.trans g).connectedComponentEquiv =
      f.connectedComponentEquiv.trans g.connectedComponentEquiv := by
  ext1 C
  simp [connectedComponentEquiv]

/-- The number of connected components is invariant under multigraph isomorphism. -/
theorem componentCount_eq (f : Iso G H) : H.componentCount = G.componentCount := by
  rw [componentCount_def, componentCount_def]
  exact Nat.card_congr f.connectedComponentEquiv.symm

end Iso

end Graph

namespace SimpleGraph.Subgraph

variable {α : Type u} {H : SimpleGraph α} {S : H.Subgraph}

@[simp]
theorem isForest_toGraph_iff : S.toGraph.IsForest ↔ S.coe.IsAcyclic :=
  S.ofSimpleGraphCoeIso.isForest_iff.trans Graph.isForest_ofSimpleGraph_iff

@[simp]
theorem isEdgeConnected_toGraph_iff (k : ℕ) :
    S.toGraph.IsEdgeConnected k ↔ S.coe.IsEdgeConnected k :=
  (S.ofSimpleGraphCoeIso.isEdgeConnected_iff k).trans
    (Graph.isEdgeConnected_ofSimpleGraph_iff S.coe k)

@[simp]
theorem edgeConnectivity_toGraph : S.toGraph.edgeConnectivity = S.coe.edgeConnectivity :=
  S.ofSimpleGraphCoeIso.edgeConnectivity_eq.trans (Graph.edgeConnectivity_ofSimpleGraph S.coe)

end SimpleGraph.Subgraph
