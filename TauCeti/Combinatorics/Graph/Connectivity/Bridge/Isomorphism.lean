/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Forest
public import TauCeti.Combinatorics.Graph.Connectivity.Isomorphism

/-!
# Isomorphisms of bridge forests

An isomorphism of multigraphs carries the components left after deleting all bridges to the
corresponding components of the other graph. It therefore induces an isomorphism of their
bridge forests, retaining the original bridge identities. The vertex-to-component maps commute
with this isomorphism, so bridge-forest paths and separation certificates can be relabelled
using the existing walk transport API.

The constructions require no finiteness and include isolated vertices, loops, parallel edges,
and empty graphs.
-/

public section

open Set

universe u v u' v' u'' v''

namespace Graph.Iso

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

private noncomputable def bridgeComponentMap (f : Iso G H) :
    G.BridgeComponent → H.BridgeComponent :=
  fun C ↦ SimpleGraph.ConnectedComponent.lift
    (G := (G.deleteEdges G.bridgeSet).toSimpleGraph)
    (fun x ↦ H.bridgeComponentOf
      (f.vertexEquiv ⟨x.val, by simpa using x.property⟩)
      (f.vertexEquiv ⟨x.val, by simpa using x.property⟩).property)
    (fun x y p _ ↦ (H.bridgeComponentOf_eq_bridgeComponentOf_iff _ _).mpr (by
      rw [← f.mapEdgeSet_bridgeSet]
      exact (f.reachable_deleteEdges_mapEdgeSet_iff G.bridgeSet
        ⟨x.val, by simpa using x.property⟩ ⟨y.val, by simpa using y.property⟩).mpr
        (Graph.toSimpleGraph_reachable_iff.mp p.reachable)))
    ((G.deleteEdges G.bridgeSet).connectedComponentEquiv C)

private theorem bridgeComponentMap_bridgeComponentOf (f : Iso G H) (x : α) (hx : x ∈ V(G)) :
    f.bridgeComponentMap (G.bridgeComponentOf x hx) =
      H.bridgeComponentOf (f.vertexEquiv ⟨x, hx⟩) (f.vertexEquiv ⟨x, hx⟩).property := by
  simp [bridgeComponentMap]

/-- A multigraph isomorphism identifies the components left after deleting all bridges. -/
noncomputable def bridgeComponentEquiv (f : Iso G H) : G.BridgeComponent ≃ H.BridgeComponent where
  toFun := f.bridgeComponentMap
  invFun := f.symm.bridgeComponentMap
  left_inv C := by
    obtain ⟨x, hx, rfl⟩ := C.exists_bridgeComponentOf_eq
    simp only [bridgeComponentMap_bridgeComponentOf]
    simp
  right_inv C := by
    obtain ⟨x, hx, rfl⟩ := C.exists_bridgeComponentOf_eq
    simp only [bridgeComponentMap_bridgeComponentOf]
    simp

/-- The bridge component of a vertex maps to the bridge component of its image. -/
@[simp]
theorem bridgeComponentEquiv_bridgeComponentOf (f : Iso G H) (x : α) (hx : x ∈ V(G)) :
    f.bridgeComponentEquiv (G.bridgeComponentOf x hx) =
      H.bridgeComponentOf (f.vertexEquiv ⟨x, hx⟩) (f.vertexEquiv ⟨x, hx⟩).property :=
  bridgeComponentMap_bridgeComponentOf f x hx

/-- Inverse component transport is induced by the inverse graph isomorphism. -/
@[simp]
theorem bridgeComponentEquiv_symm (f : Iso G H) :
    f.symm.bridgeComponentEquiv = f.bridgeComponentEquiv.symm := by
  apply Equiv.ext
  intro C
  rfl

/-- Inverse component transport sends a vertex's component to its inverse image's component. -/
@[simp]
theorem bridgeComponentEquiv_symm_bridgeComponentOf (f : Iso G H) (y : α') (hy : y ∈ V(H)) :
    f.bridgeComponentEquiv.symm (H.bridgeComponentOf y hy) =
      G.bridgeComponentOf (f.vertexEquiv.symm ⟨y, hy⟩) (f.vertexEquiv.symm ⟨y, hy⟩).property := by
  simpa only [bridgeComponentEquiv_symm, symm_vertexEquiv] using
    f.symm.bridgeComponentEquiv_bridgeComponentOf y hy

/-- Component transport along the identity fixes every bridge component. -/
@[simp]
theorem bridgeComponentEquiv_refl : (refl G).bridgeComponentEquiv = Equiv.refl _ := by
  apply Equiv.ext
  intro C
  obtain ⟨x, hx, rfl⟩ := C.exists_bridgeComponentOf_eq
  simp

/-- Bridge-component transport respects composition. -/
@[simp]
theorem bridgeComponentEquiv_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).bridgeComponentEquiv = f.bridgeComponentEquiv.trans g.bridgeComponentEquiv := by
  apply Equiv.ext
  intro C
  obtain ⟨x, hx, rfl⟩ := C.exists_bridgeComponentOf_eq
  simp

/-- Component transport preserves and reflects membership of actual vertices. -/
theorem vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff (f : Iso G H)
    (C : G.BridgeComponent)
    (x : V(G)) :
    (f.vertexEquiv x : α') ∈ V((f.bridgeComponentEquiv C).val) ↔ (x : α) ∈ V(C.val) := by
  obtain ⟨y, hy, rfl⟩ := C.exists_bridgeComponentOf_eq
  rw [bridgeComponentEquiv_bridgeComponentOf, Graph.mem_vertexSet_bridgeComponentOf_iff,
    Graph.mem_vertexSet_bridgeComponentOf_iff, ← f.mapEdgeSet_bridgeSet]
  exact f.reachable_deleteEdges_mapEdgeSet_iff G.bridgeSet ⟨y, hy⟩ x

/-- Membership in a transported bridge component is membership of the inverse image. -/
@[simp]
theorem mem_vertexSet_bridgeComponentEquiv_iff (f : Iso G H) (C : G.BridgeComponent)
    (y : V(H)) :
    (y : α') ∈ V((f.bridgeComponentEquiv C).val) ↔
      (f.vertexEquiv.symm y : α) ∈ V(C.val) := by
  simpa using f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff C (f.vertexEquiv.symm y)

/-- Membership in an inverse-transported bridge component is membership of the image. -/
@[simp]
theorem mem_vertexSet_bridgeComponentEquiv_symm_iff (f : Iso G H) (D : H.BridgeComponent)
    (x : V(G)) :
    (x : α) ∈ V((f.bridgeComponentEquiv.symm D).val) ↔
      (f.vertexEquiv x : α') ∈ V(D.val) := by
  simpa using f.symm.mem_vertexSet_bridgeComponentEquiv_iff D x

/-- The vertex set of a transported bridge component is the transported vertex set. -/
theorem vertexSet_bridgeComponentEquiv (f : Iso G H) (C : G.BridgeComponent) :
    V((f.bridgeComponentEquiv C).val) = f.mapVertexSet V(C.val) := by
  ext y
  by_cases hy : y ∈ V(H)
  · exact (f.mem_vertexSet_bridgeComponentEquiv_iff C ⟨y, hy⟩).trans
      (f.mem_mapVertexSet_iff V(C.val) ⟨y, hy⟩).symm
  · exact iff_of_false (fun h ↦ hy (Graph.BridgeComponent.mem_vertexSet h))
      (fun h ↦ hy (f.mapVertexSet_subset_vertexSet _ h))

private def bridgeForestEdgeEquiv (f : Iso G H) : E(G.bridgeForest) ≃ E(H.bridgeForest) :=
  (Equiv.subtypeEquivRight (p := (· ∈ E(G.bridgeForest)))
    (q := G.IsBridge) (fun e ↦ by simp)).trans <|
    (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ E(G))) (q := G.IsBridge)
      (fun he ↦ he.mem_edgeSet)).symm.trans <|
    (f.edgeEquiv.subtypeEquiv (p := fun e ↦ G.IsBridge e.val) (q := fun e ↦ H.IsBridge e.val)
      (fun e ↦ (f.isBridge_edgeEquiv_iff e).symm)).trans <|
    (Equiv.subtypeSubtypeEquivSubtype (fun he ↦ he.mem_edgeSet)).trans <|
    Equiv.subtypeEquivRight (p := H.IsBridge) (q := (· ∈ E(H.bridgeForest)))
      (fun e ↦ by simp)

private theorem coe_bridgeForestEdgeEquiv (f : Iso G H) (e : E(G.bridgeForest)) :
    (f.bridgeForestEdgeEquiv e : β') =
      f.edgeEquiv ⟨e.val, (Graph.mem_bridgeSet.mp (by simpa using e.property)).mem_edgeSet⟩ :=
  rfl

/-- An isomorphism of multigraphs induces an isomorphism of their bridge forests, using the
original edge equivalence on bridge identities. -/
noncomputable def bridgeForestIso (f : Iso G H) : Iso G.bridgeForest H.bridgeForest where
  vertexEquiv := (Equiv.subtypeUnivEquiv (p := (· ∈ V(G.bridgeForest))) (by simp)).trans
    (f.bridgeComponentEquiv.trans
      (Equiv.subtypeUnivEquiv (p := (· ∈ V(H.bridgeForest))) (by simp)).symm)
  edgeEquiv := f.bridgeForestEdgeEquiv
  map_isLink_iff e C D := by
    rw [coe_bridgeForestEdgeEquiv]
    simp only [Equiv.trans_apply, Equiv.subtypeUnivEquiv]
    rw [Graph.bridgeForest_isLink, Graph.bridgeForest_isLink]
    refine and_congr (f.isBridge_edgeEquiv_iff _) (Iff.intro ?_ ?_)
    · rintro ⟨x, hx, y, hy, hxy⟩
      let x' := f.vertexEquiv.symm ⟨x, Graph.BridgeComponent.mem_vertexSet hx⟩
      let y' := f.vertexEquiv.symm ⟨y, Graph.BridgeComponent.mem_vertexSet hy⟩
      have hx' : (x' : α) ∈ V(C.val.val) :=
        (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff C.val x').mp (by simpa [x'] using hx)
      have hy' : (y' : α) ∈ V(D.val.val) :=
        (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff D.val y').mp (by simpa [y'] using hy)
      exact ⟨x', hx', y', hy', (f.map_isLink_iff _ x' y').mp (by simpa [x', y'] using hxy)⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨f.vertexEquiv ⟨x, hxy.left_mem⟩,
        (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff C.val ⟨x, hxy.left_mem⟩).mpr hx,
        f.vertexEquiv ⟨y, hxy.right_mem⟩,
        (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff D.val ⟨y, hxy.right_mem⟩).mpr hy,
        (f.map_isLink_iff _ _ _).mpr hxy⟩

/-- The induced forest isomorphism acts on vertices by bridge-component transport. -/
@[simp]
theorem coe_bridgeForestIso_vertexEquiv_apply (f : Iso G H) (C : V(G.bridgeForest)) :
    (f.bridgeForestIso.vertexEquiv C : H.BridgeComponent) = f.bridgeComponentEquiv C.val :=
  (rfl)

/-- The induced forest isomorphism retains the image of each original bridge identity. -/
@[simp]
theorem coe_bridgeForestIso_edgeEquiv_apply (f : Iso G H) (e : E(G.bridgeForest)) :
    (f.bridgeForestIso.edgeEquiv e : β') =
      f.edgeEquiv ⟨e.val, (Graph.mem_bridgeSet.mp (by simpa using e.property)).mem_edgeSet⟩ :=
  coe_bridgeForestEdgeEquiv f e

/-- The inverse forest vertex equivalence acts by inverse bridge-component transport. -/
@[simp]
theorem coe_bridgeForestIso_vertexEquiv_symm_apply (f : Iso G H) (D : V(H.bridgeForest)) :
    (f.bridgeForestIso.vertexEquiv.symm D : G.BridgeComponent) =
      f.bridgeComponentEquiv.symm D.val :=
  (rfl)

/-- The inverse forest edge equivalence retains the inverse image of each bridge identity. -/
@[simp]
theorem coe_bridgeForestIso_edgeEquiv_symm_apply (f : Iso G H) (e : E(H.bridgeForest)) :
    (f.bridgeForestIso.edgeEquiv.symm e : β) =
      f.edgeEquiv.symm ⟨e.val, (Graph.mem_bridgeSet.mp (by simpa using e.property)).mem_edgeSet⟩ :=
  (rfl)

/-- The identity multigraph isomorphism induces the identity bridge-forest isomorphism. -/
@[simp]
theorem bridgeForestIso_refl : (refl G).bridgeForestIso = refl G.bridgeForest := by
  apply Iso.ext
  · apply Equiv.ext
    intro C
    apply Subtype.ext
    simp
  · apply Equiv.ext
    intro e
    apply Subtype.ext
    simp

/-- Taking bridge forests commutes with composition of multigraph isomorphisms. -/
@[simp]
theorem bridgeForestIso_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).bridgeForestIso = f.bridgeForestIso.trans g.bridgeForestIso := by
  apply Iso.ext
  · apply Equiv.ext
    intro C
    apply Subtype.ext
    simp
  · apply Equiv.ext
    intro e
    apply Subtype.ext
    simp

/-- Inverting an isomorphism inverts the induced bridge-forest isomorphism. -/
@[simp]
theorem bridgeForestIso_symm (f : Iso G H) :
    f.symm.bridgeForestIso = f.bridgeForestIso.symm := by
  have h := bridgeForestIso_trans f.symm f
  rw [symm_trans_self, bridgeForestIso_refl] at h
  have h' := congrArg (fun g ↦ g.trans f.bridgeForestIso.symm) h
  simpa only [trans_assoc, self_trans_symm, trans_refl, refl_trans] using h'.symm

private theorem toBridgeForest_mapWalk_edges (f : Iso G H) {x y : α} (p : G.Walk x y)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    ((f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).toBridgeForest
      (f.vertexEquiv ⟨x, hx⟩).property (f.vertexEquiv ⟨y, hy⟩).property).edges =
      (f.bridgeForestIso.mapWalk (x := ⟨G.bridgeComponentOf x hx, by simp⟩)
        (y := ⟨G.bridgeComponentOf y hy, by simp⟩) (p.toBridgeForest hx hy)).edges := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      rw [f.mapWalk_cons (x := ⟨x, hx⟩) (y := ⟨y, h.right_mem⟩) (z := ⟨z, hy⟩)]
      by_cases he : G.IsBridge e
      · have he' := (f.isBridge_edgeEquiv_iff ⟨e, h.edge_mem⟩).mpr he
        rw [Graph.Walk.toBridgeForest_cons_of_isBridge _ _ he',
          Graph.Walk.toBridgeForest_cons_of_isBridge _ _ he]
        rw [f.bridgeForestIso.mapWalk_cons
          (x := ⟨G.bridgeComponentOf x hx, by simp⟩)
          (y := ⟨G.bridgeComponentOf y h.right_mem, by simp⟩)
          (z := ⟨G.bridgeComponentOf z hy, by simp⟩)]
        simp only [Graph.Walk.edges_cons, coe_bridgeForestIso_edgeEquiv_apply,
          ih h.right_mem hy]
      · have he' : ¬ H.IsBridge (f.edgeEquiv ⟨e, h.edge_mem⟩) :=
          fun h' ↦ he ((f.isBridge_edgeEquiv_iff ⟨e, h.edge_mem⟩).mp h')
        rw [Graph.Walk.toBridgeForest_cons_of_not_isBridge _ _ he',
          Graph.Walk.toBridgeForest_cons_of_not_isBridge _ _ he,
          Graph.Walk.edges_copy, ih h.right_mem hy]
        rw [edges_mapWalk, edges_mapWalk]
        congr 2
        apply Subtype.val_injective.list_map
        rw [← List.unattach, ← List.unattach, Graph.Walk.edgesAttach_unattach,
          Graph.Walk.edgesAttach_unattach, Graph.Walk.edges_copy]

/-- Projecting a transported walk is transporting its bridge-forest projection. -/
@[simp]
theorem toBridgeForest_mapWalk (f : Iso G H) {x y : V(G)} (p : G.Walk x y) :
    (f.mapWalk p).toBridgeForest (f.vertexEquiv x).property (f.vertexEquiv y).property =
      (f.bridgeForestIso.mapWalk
        (x := ⟨G.bridgeComponentOf x x.property, by simp⟩)
        (y := ⟨G.bridgeComponentOf y y.property, by simp⟩)
        (p.toBridgeForest x.property y.property)).copy (by simp) (by simp) := by
  apply Graph.Walk.ext_edges
  rw [Graph.Walk.edges_copy]
  exact toBridgeForest_mapWalk_edges f p x.property y.property

/-- Forest edge-set transport is original edge-set transport restricted to bridges. -/
theorem mapEdgeSet_bridgeForestIso (f : Iso G H) (F : Set β) :
    f.bridgeForestIso.mapEdgeSet F = f.mapEdgeSet F ∩ H.bridgeSet := by
  ext e
  by_cases he : H.IsBridge e
  · have h := f.bridgeForestIso.mem_mapEdgeSet_iff F
      ⟨e, by simpa using Graph.mem_bridgeSet.mpr he⟩
    simpa only [coe_bridgeForestIso_edgeEquiv_symm_apply, ← f.mem_mapEdgeSet_iff,
      mem_inter_iff, Graph.mem_bridgeSet, he, and_true] using h
  · exact iff_of_false
      (fun h ↦ he (Graph.mem_bridgeSet.mp (by
        simpa using f.bridgeForestIso.mapEdgeSet_subset_edgeSet F h)))
      (fun h ↦ he (Graph.mem_bridgeSet.mp h.2))

/-- A set of bridges has the same transported identities in the graph and its bridge forest. -/
theorem mapEdgeSet_bridgeForestIso_of_subset (f : Iso G H) {F : Set β}
    (hF : F ⊆ G.bridgeSet) : f.bridgeForestIso.mapEdgeSet F = f.mapEdgeSet F := by
  rw [mapEdgeSet_bridgeForestIso, inter_eq_left.mpr
    ((f.mapEdgeSet_mono hF).trans_eq f.mapEdgeSet_bridgeSet)]

end Graph.Iso
