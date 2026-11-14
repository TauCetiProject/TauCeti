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
      (f.vertexEquiv ⟨x.1, by simpa using x.2⟩)
      (f.vertexEquiv ⟨x.1, by simpa using x.2⟩).2)
    (fun x y p _ ↦ (H.bridgeComponentOf_eq_bridgeComponentOf_iff _ _).mpr (by
      rw [← f.mapEdgeSet_bridgeSet]
      exact (f.reachable_deleteEdges_mapEdgeSet_iff G.bridgeSet
        ⟨x.1, by simpa using x.2⟩ ⟨y.1, by simpa using y.2⟩).mpr
        (Graph.toSimpleGraph_reachable_iff.mp p.reachable)))
    ((G.deleteEdges G.bridgeSet).connectedComponentEquiv C)

private theorem bridgeComponentMap_bridgeComponentOf (f : Iso G H) (x : α) (hx : x ∈ V(G)) :
    f.bridgeComponentMap (G.bridgeComponentOf x hx) =
      H.bridgeComponentOf (f.vertexEquiv ⟨x, hx⟩) (f.vertexEquiv ⟨x, hx⟩).2 := by
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
      H.bridgeComponentOf (f.vertexEquiv ⟨x, hx⟩) (f.vertexEquiv ⟨x, hx⟩).2 :=
  bridgeComponentMap_bridgeComponentOf f x hx

/-- Inverse component transport is induced by the inverse graph isomorphism. -/
@[simp]
theorem bridgeComponentEquiv_symm (f : Iso G H) :
    f.symm.bridgeComponentEquiv = f.bridgeComponentEquiv.symm := by
  apply Equiv.ext
  intro C
  rfl

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
@[simp]
theorem mem_vertexSet_bridgeComponentEquiv_iff (f : Iso G H) (C : G.BridgeComponent)
    (x : V(G)) :
    (f.vertexEquiv x : α') ∈ V((f.bridgeComponentEquiv C).1) ↔ (x : α) ∈ V(C.1) := by
  obtain ⟨y, hy, rfl⟩ := C.exists_bridgeComponentOf_eq
  rw [bridgeComponentEquiv_bridgeComponentOf, Graph.mem_vertexSet_bridgeComponentOf_iff,
    Graph.mem_vertexSet_bridgeComponentOf_iff, ← f.mapEdgeSet_bridgeSet]
  exact f.reachable_deleteEdges_mapEdgeSet_iff G.bridgeSet ⟨y, hy⟩ x

private def bridgeForestEdgeEquiv (f : Iso G H) : E(G.bridgeForest) ≃ E(H.bridgeForest) :=
  (Equiv.subtypeEquivRight (p := (· ∈ E(G.bridgeForest)))
    (q := G.IsBridge) (fun e ↦ by simp)).trans <|
    (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ E(G))) (q := G.IsBridge)
      (fun he ↦ he.mem_edgeSet)).symm.trans <|
    (f.edgeEquiv.subtypeEquiv (p := fun e ↦ G.IsBridge e.1) (q := fun e ↦ H.IsBridge e.1)
      (fun e ↦ (f.isBridge_edgeEquiv_iff e).symm)).trans <|
    (Equiv.subtypeSubtypeEquivSubtype (fun he ↦ he.mem_edgeSet)).trans <|
    Equiv.subtypeEquivRight (p := H.IsBridge) (q := (· ∈ E(H.bridgeForest)))
      (fun e ↦ by simp)

private theorem coe_bridgeForestEdgeEquiv (f : Iso G H) (e : E(G.bridgeForest)) :
    (f.bridgeForestEdgeEquiv e : β') =
      f.edgeEquiv ⟨e.1, (Graph.mem_bridgeSet.mp (by simpa using e.2)).mem_edgeSet⟩ :=
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
      have hx' : (x' : α) ∈ V(C.1.1) :=
        (f.mem_vertexSet_bridgeComponentEquiv_iff C.1 x').mp (by simpa [x'] using hx)
      have hy' : (y' : α) ∈ V(D.1.1) :=
        (f.mem_vertexSet_bridgeComponentEquiv_iff D.1 y').mp (by simpa [y'] using hy)
      exact ⟨x', hx', y', hy', (f.map_isLink_iff _ x' y').mp (by simpa [x', y'] using hxy)⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨f.vertexEquiv ⟨x, hxy.left_mem⟩,
        (f.mem_vertexSet_bridgeComponentEquiv_iff C.1 ⟨x, hxy.left_mem⟩).mpr hx,
        f.vertexEquiv ⟨y, hxy.right_mem⟩,
        (f.mem_vertexSet_bridgeComponentEquiv_iff D.1 ⟨y, hxy.right_mem⟩).mpr hy,
        (f.map_isLink_iff _ _ _).mpr hxy⟩

/-- The induced forest isomorphism acts on vertices by bridge-component transport. -/
@[simp]
theorem bridgeForestIso_vertexEquiv_apply (f : Iso G H) (C : V(G.bridgeForest)) :
    (f.bridgeForestIso.vertexEquiv C : H.BridgeComponent) = f.bridgeComponentEquiv C.1 :=
  (rfl)

/-- The induced forest isomorphism retains the image of each original bridge identity. -/
@[simp]
theorem coe_bridgeForestIso_edgeEquiv_apply (f : Iso G H) (e : E(G.bridgeForest)) :
    (f.bridgeForestIso.edgeEquiv e : β') =
      f.edgeEquiv ⟨e.1, (Graph.mem_bridgeSet.mp (by simpa using e.2)).mem_edgeSet⟩ :=
  coe_bridgeForestEdgeEquiv f e

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

end Graph.Iso
