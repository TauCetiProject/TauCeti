/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Forest
public import TauCeti.Combinatorics.Graph.Connectivity.Isomorphism
public import TauCeti.Combinatorics.Graph.Isomorphism.Subgraph
import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Paths

/-!
# Isomorphism invariance of bridge components and bridge forests

A multigraph isomorphism `f : Graph.Iso G H` preserves bridges, so it restricts to an
isomorphism between the bridge-deleted graphs `G.deleteEdges G.bridgeSet` and
`H.deleteEdges H.bridgeSet`. Consequently it induces an equivalence
`Graph.Iso.bridgeComponentEquiv` on bridge components, an isomorphism
`Graph.Iso.bridgeComponentIso` between each bridge component subgraph and its image, and an
isomorphism `Graph.Iso.bridgeForestIso` between the bridge forests `G.bridgeForest` and
`H.bridgeForest`.

These constructions respect identity, inversion, and composition, and commute with walk
projection (`Graph.Walk.toBridgeForest`) and the component correspondence
`Graph.connectedComponentEquivBridgeForest`; for path lifting (`Graph.Walk.liftBridgeForest`),
projecting the transported lift recovers the transported forest path. No finiteness hypotheses are
required.
-/

public section

open Set

universe u v u' v' u'' v''

namespace Graph.Iso

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
  {α'' : Type u''} {β'' : Type v''}
  {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

/-! ### Bridge components -/

private noncomputable def deleteEdgesBridgeSetIso (f : Iso G H) :
    Iso (G.deleteEdges G.bridgeSet) (H.deleteEdges H.bridgeSet) :=
  f.deleteEdgesIso fun e ↦ by simpa [mem_bridgeSet] using f.isBridge_edgeEquiv_iff e

private theorem bridgeComponentOf_eq_connectedComponentOf (G : Graph α β) {x : α}
    (hx : x ∈ V(G)) :
    G.bridgeComponentOf x hx =
      (G.deleteEdges G.bridgeSet).connectedComponentOf x (by rwa [vertexSet_deleteEdges]) :=
  ConnectedComponent.eq_connectedComponentOf (G.mem_vertexSet_bridgeComponentOf_self hx)

/-- A multigraph isomorphism induces an equivalence of bridge components. -/
noncomputable def bridgeComponentEquiv (f : Iso G H) :
    G.BridgeComponent ≃ H.BridgeComponent :=
  f.deleteEdgesBridgeSetIso.connectedComponentEquiv

/-- The bridge component of an actual vertex is sent to the bridge component of its image. -/
@[simp]
theorem bridgeComponentEquiv_bridgeComponentOf (f : Iso G H) {x : α} (hx : x ∈ V(G)) :
    f.bridgeComponentEquiv (G.bridgeComponentOf x hx) =
      H.bridgeComponentOf (f.vertexEquiv ⟨x, hx⟩) (f.vertexEquiv ⟨x, hx⟩).property := by
  rw [bridgeComponentEquiv, bridgeComponentOf_eq_connectedComponentOf,
    bridgeComponentOf_eq_connectedComponentOf,
    f.deleteEdgesBridgeSetIso.connectedComponentEquiv_connectedComponentOf]
  simp only [deleteEdgesBridgeSetIso, coe_deleteEdgesIso_vertexEquiv_apply]

/-- The inverse bridge-component equivalence sends the component of an actual vertex to the
component of its preimage. -/
@[simp]
theorem bridgeComponentEquiv_symm_bridgeComponentOf (f : Iso G H) {y : α'} (hy : y ∈ V(H)) :
    f.bridgeComponentEquiv.symm (H.bridgeComponentOf y hy) =
      G.bridgeComponentOf (f.vertexEquiv.symm ⟨y, hy⟩)
        (f.vertexEquiv.symm ⟨y, hy⟩).property := by
  rw [bridgeComponentEquiv, bridgeComponentOf_eq_connectedComponentOf,
    bridgeComponentOf_eq_connectedComponentOf,
    f.deleteEdgesBridgeSetIso.connectedComponentEquiv_symm_connectedComponentOf]
  simp only [deleteEdgesBridgeSetIso, coe_deleteEdgesIso_vertexEquiv_symm_apply]

/-- An actual vertex lies in the transported bridge component exactly when its preimage lies in
the original bridge component. -/
@[simp]
theorem vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff (f : Iso G H)
    (C : G.BridgeComponent) (x : V(G)) :
    (f.vertexEquiv x : α') ∈ V((f.bridgeComponentEquiv C).val) ↔ (x : α) ∈ V(C.val) := by
  have h := f.deleteEdgesBridgeSetIso.vertexEquiv_mem_vertexSet_connectedComponentEquiv_iff C
    ⟨x.val, by simp⟩
  simpa [bridgeComponentEquiv, deleteEdgesBridgeSetIso] using h

/-- An actual edge lies in the transported bridge component exactly when its preimage lies in the
original bridge component. -/
@[simp]
theorem edgeEquiv_mem_edgeSet_bridgeComponentEquiv_iff (f : Iso G H)
    (C : G.BridgeComponent) (e : E(G)) :
    (f.edgeEquiv e : β') ∈ E((f.bridgeComponentEquiv C).val) ↔ (e : β) ∈ E(C.val) := by
  by_cases he : (e : β) ∈ G.bridgeSet
  · have hbr : (f.edgeEquiv e : β') ∈ H.bridgeSet := by
      rw [mem_bridgeSet, f.isBridge_edgeEquiv_iff]
      exact mem_bridgeSet.mp he
    exact iff_of_false
      (fun hmem ↦ ((f.bridgeComponentEquiv C).property.le.edgeSet_mono hmem).2 hbr)
      (fun hmem ↦ (C.property.le.edgeSet_mono hmem).2 he)
  · let e' : E(G.deleteEdges G.bridgeSet) := ⟨e, e.property, he⟩
    have h := f.deleteEdgesBridgeSetIso.edgeEquiv_mem_edgeSet_connectedComponentEquiv_iff C e'
    simpa [bridgeComponentEquiv, deleteEdgesBridgeSetIso, e'] using h

/-- An actual vertex lies in the pulled-back bridge component exactly when its image lies in the
original bridge component. -/
@[simp]
theorem vertexEquiv_symm_mem_vertexSet_bridgeComponentEquiv_symm_iff (f : Iso G H)
    (D : H.BridgeComponent) (y : V(H)) :
    (f.vertexEquiv.symm y : α) ∈ V((f.bridgeComponentEquiv.symm D).val) ↔ (y : α') ∈ V(D.val) := by
  have h :=
    f.deleteEdgesBridgeSetIso.vertexEquiv_symm_mem_vertexSet_connectedComponentEquiv_symm_iff
      D ⟨y.val, by simp⟩
  simpa [bridgeComponentEquiv, deleteEdgesBridgeSetIso] using h

/-- An actual edge lies in the pulled-back bridge component exactly when its image lies in the
original bridge component. -/
@[simp]
theorem edgeEquiv_symm_mem_edgeSet_bridgeComponentEquiv_symm_iff (f : Iso G H)
    (D : H.BridgeComponent) (e : E(H)) :
    (f.edgeEquiv.symm e : β) ∈ E((f.bridgeComponentEquiv.symm D).val) ↔ (e : β') ∈ E(D.val) := by
  have h := f.edgeEquiv_mem_edgeSet_bridgeComponentEquiv_iff (f.bridgeComponentEquiv.symm D)
    (f.edgeEquiv.symm e)
  simpa using h.symm

/-- The vertices of a transported bridge component are the transported vertices of the component. -/
theorem vertexSet_bridgeComponentEquiv (f : Iso G H) (C : G.BridgeComponent) :
    V((f.bridgeComponentEquiv C).val) = f.mapVertexSet V(C.val) := by
  simpa [bridgeComponentEquiv, deleteEdgesBridgeSetIso] using
    f.deleteEdgesBridgeSetIso.vertexSet_connectedComponentEquiv C

/-- The edges of a transported bridge component are the transported edges of the component. -/
theorem edgeSet_bridgeComponentEquiv (f : Iso G H) (C : G.BridgeComponent) :
    E((f.bridgeComponentEquiv C).val) = f.mapEdgeSet E(C.val) := by
  ext e
  by_cases he : e ∈ E(H)
  · let e' : E(H) := ⟨e, he⟩
    exact (f.edgeEquiv_symm_mem_edgeSet_bridgeComponentEquiv_symm_iff
      (f.bridgeComponentEquiv C) e').symm.trans
      (by simpa [e'] using (f.mem_mapEdgeSet_iff E(C.val) e').symm)
  · exact iff_of_false
      (fun h ↦ he ((f.bridgeComponentEquiv C).property.le.edgeSet_mono h).1)
      (fun h ↦ he (f.mapEdgeSet_subset_edgeSet _ h))

/-- The identity isomorphism acts identically on bridge components. -/
@[simp]
theorem bridgeComponentEquiv_refl (G : Graph α β) :
    (refl G).bridgeComponentEquiv = Equiv.refl G.BridgeComponent := by
  ext1 C
  obtain ⟨x, hx, rfl⟩ := C.exists_bridgeComponentOf_eq
  simp

/-- Inversion of multigraph isomorphisms inverts the induced bridge-component equivalence. -/
@[simp]
theorem bridgeComponentEquiv_symm (f : Iso G H) :
    f.symm.bridgeComponentEquiv = f.bridgeComponentEquiv.symm := by
  ext1 D
  obtain ⟨y, hy, rfl⟩ := D.exists_bridgeComponentOf_eq
  simp

/-- Composition of multigraph isomorphisms composes their bridge-component equivalences. -/
@[simp]
theorem bridgeComponentEquiv_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).bridgeComponentEquiv = f.bridgeComponentEquiv.trans g.bridgeComponentEquiv := by
  ext1 C
  obtain ⟨x, hx, rfl⟩ := C.exists_bridgeComponentOf_eq
  simp

/-- A multigraph isomorphism restricts to an isomorphism between each bridge component and the
corresponding bridge component. -/
noncomputable def bridgeComponentIso (f : Iso G H) (C : G.BridgeComponent) :
    Iso C.val (f.bridgeComponentEquiv C).val :=
  f.deleteEdgesBridgeSetIso.connectedComponentIso C

/-- The vertex equivalence of a restricted bridge-component isomorphism acts by the original vertex
equivalence. -/
@[simp]
theorem coe_bridgeComponentIso_vertexEquiv_apply (f : Iso G H) (C : G.BridgeComponent)
    (x : V(C.val)) :
    ((f.bridgeComponentIso C).vertexEquiv x : α') =
      f.vertexEquiv ⟨x, BridgeComponent.mem_vertexSet x.property⟩ :=
  (f.deleteEdgesBridgeSetIso.coe_connectedComponentIso_vertexEquiv_apply C x).trans
    (by simp [deleteEdgesBridgeSetIso])

/-- The inverse vertex equivalence of a restricted bridge-component isomorphism acts by the
original inverse vertex equivalence. -/
@[simp]
theorem coe_bridgeComponentIso_vertexEquiv_symm_apply (f : Iso G H) (C : G.BridgeComponent)
    (y : V((f.bridgeComponentEquiv C).val)) :
    ((f.bridgeComponentIso C).vertexEquiv.symm y : α) =
      f.vertexEquiv.symm ⟨y, BridgeComponent.mem_vertexSet y.property⟩ :=
  (f.deleteEdgesBridgeSetIso.coe_connectedComponentIso_vertexEquiv_symm_apply C y).trans
    (by simp [deleteEdgesBridgeSetIso])

/-- The edge equivalence of a restricted bridge-component isomorphism acts by the original edge
equivalence. -/
@[simp]
theorem coe_bridgeComponentIso_edgeEquiv_apply (f : Iso G H) (C : G.BridgeComponent)
    (e : E(C.val)) :
    ((f.bridgeComponentIso C).edgeEquiv e : β') =
      f.edgeEquiv ⟨e, (C.property.le.edgeSet_mono e.property).1⟩ :=
  (f.deleteEdgesBridgeSetIso.coe_connectedComponentIso_edgeEquiv_apply C e).trans
    (by simp [deleteEdgesBridgeSetIso])

/-- The inverse edge equivalence of a restricted bridge-component isomorphism acts by the original
inverse edge equivalence. -/
@[simp]
theorem coe_bridgeComponentIso_edgeEquiv_symm_apply (f : Iso G H) (C : G.BridgeComponent)
    (e : E((f.bridgeComponentEquiv C).val)) :
    ((f.bridgeComponentIso C).edgeEquiv.symm e : β) =
      f.edgeEquiv.symm ⟨e, ((f.bridgeComponentEquiv C).property.le.edgeSet_mono e.property).1⟩ :=
  (f.deleteEdgesBridgeSetIso.coe_connectedComponentIso_edgeEquiv_symm_apply C e).trans
    (by simp [deleteEdgesBridgeSetIso])

/-! ### The bridge forest -/

/-- A multigraph isomorphism induces an isomorphism between the bridge forests. -/
noncomputable def bridgeForestIso (f : Iso G H) : Iso G.bridgeForest H.bridgeForest where
  vertexEquiv := f.bridgeComponentEquiv.subtypeEquiv fun _ ↦ by simp
  edgeEquiv :=
    { toFun e := ⟨f.edgeEquiv ⟨e,
          G.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset e.property)⟩,
        by
          rw [edgeSet_bridgeForest, mem_bridgeSet, f.isBridge_edgeEquiv_iff]
          exact mem_bridgeSet.mp (edgeSet_bridgeForest.subset e.property)⟩
      invFun e := ⟨f.edgeEquiv.symm
          ⟨e, H.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset e.property)⟩,
        by
          rw [edgeSet_bridgeForest, mem_bridgeSet, ← f.isBridge_edgeEquiv_iff,
            Equiv.apply_symm_apply]
          exact mem_bridgeSet.mp (edgeSet_bridgeForest.subset e.property)⟩
      left_inv _ := Subtype.ext (by simp)
      right_inv _ := Subtype.ext (by simp) }
  map_isLink_iff e C D := by
    let e' : E(G) := ⟨e, G.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset e.property)⟩
    have hbr := f.isBridge_edgeEquiv_iff e'
    simp only [bridgeForest_isLink]
    constructor
    · rintro ⟨he', x', hx', y', hy', hl⟩
      refine ⟨hbr.mp he', f.vertexEquiv.symm ⟨x', hl.left_mem⟩, ?_,
        f.vertexEquiv.symm ⟨y', hl.right_mem⟩, ?_, ?_⟩
      · exact (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff C.val _).mp (by simpa using hx')
      · exact (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff D.val _).mp (by simpa using hy')
      · rw [← f.map_isLink_iff e']
        simpa [e'] using hl
    · rintro ⟨he, x, hx, y, hy, hl⟩
      refine ⟨hbr.mpr he, f.vertexEquiv ⟨x, BridgeComponent.mem_vertexSet hx⟩,
        (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff C.val _).mpr hx,
        f.vertexEquiv ⟨y, BridgeComponent.mem_vertexSet hy⟩,
        (f.vertexEquiv_mem_vertexSet_bridgeComponentEquiv_iff D.val _).mpr hy, ?_⟩
      exact f.map_isLink hl

/-- The vertex equivalence of `bridgeForestIso` acts by `bridgeComponentEquiv`. -/
@[simp]
theorem coe_bridgeForestIso_vertexEquiv_apply (f : Iso G H) (C : V(G.bridgeForest)) :
    ((f.bridgeForestIso.vertexEquiv C : H.BridgeComponent)) = f.bridgeComponentEquiv C.val :=
  (rfl)

/-- The inverse vertex equivalence of `bridgeForestIso` acts by `bridgeComponentEquiv.symm`. -/
@[simp]
theorem coe_bridgeForestIso_vertexEquiv_symm_apply (f : Iso G H) (D : V(H.bridgeForest)) :
    ((f.bridgeForestIso.vertexEquiv.symm D : G.BridgeComponent)) =
      f.bridgeComponentEquiv.symm D.val :=
  (rfl)

/-- The edge equivalence of `bridgeForestIso` acts by the original edge equivalence. -/
@[simp]
theorem coe_bridgeForestIso_edgeEquiv_apply (f : Iso G H) (e : E(G.bridgeForest)) :
    (f.bridgeForestIso.edgeEquiv e : β') =
      f.edgeEquiv ⟨e, G.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset e.property)⟩ :=
  (rfl)

/-- The inverse edge equivalence of `bridgeForestIso` acts by the original inverse edge
equivalence. -/
@[simp]
theorem coe_bridgeForestIso_edgeEquiv_symm_apply (f : Iso G H) (e : E(H.bridgeForest)) :
    (f.bridgeForestIso.edgeEquiv.symm e : β) =
      f.edgeEquiv.symm ⟨e, H.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset e.property)⟩ :=
  (rfl)

/-- The bridge-forest isomorphism of the identity is the identity isomorphism. -/
@[simp]
theorem bridgeForestIso_refl (G : Graph α β) :
    (refl G).bridgeForestIso = refl G.bridgeForest := by
  ext <;> simp

/-- Inversion commutes with the bridge-forest isomorphism construction. -/
@[simp]
theorem bridgeForestIso_symm (f : Iso G H) :
    f.symm.bridgeForestIso = f.bridgeForestIso.symm := by
  ext <;> simp

/-- Composition commutes with the bridge-forest isomorphism construction. -/
@[simp]
theorem bridgeForestIso_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).bridgeForestIso = f.bridgeForestIso.trans g.bridgeForestIso := by
  ext <;> simp

/-! ### Walks and connected components -/

private theorem walk_cons_eq_copy_cons {G : Graph α β} {u u' v v' w w' : α} {e : β}
    {h : G.IsLink e u v} {p : G.Walk v w}
    {h' : G.IsLink e u' v'} {p' : G.Walk v' w'}
    (hu : u' = u) (hv : v' = v) (hw : w' = w)
    (hp : p = p'.copy hv hw) :
    Walk.cons e h p = (Walk.cons e h' p').copy hu hw := by
  subst hu hv hw hp
  simp

private theorem toBridgeForest_mapWalk_aux (f : Iso G H) {x y : α} (p : G.Walk x y)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    ((f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).toBridgeForest
      (f.vertexEquiv ⟨x, hx⟩).property (f.vertexEquiv ⟨y, hy⟩).property) =
      (f.bridgeForestIso.mapWalk (x := ⟨G.bridgeComponentOf x hx, by simp⟩)
        (y := ⟨G.bridgeComponentOf y hy, by simp⟩)
        (p.toBridgeForest hx hy)).copy
          (by simp) (by simp) := by
  classical
  induction p with
  | nil =>
    cases Subsingleton.elim hx hy
    simp
  | @cons x y z e h p ih =>
    have hcons : f.mapWalk (x := (⟨x, hx⟩ : V(G))) (y := (⟨z, hy⟩ : V(G))) (.cons e h p) =
        .cons (f.edgeEquiv ⟨e, h.edge_mem⟩) (f.map_isLink h)
          (f.mapWalk (x := (⟨y, h.right_mem⟩ : V(G))) (y := (⟨z, hy⟩ : V(G))) p) :=
      f.mapWalk_cons (x := ⟨x, hx⟩) (y := ⟨y, h.right_mem⟩) (z := ⟨z, hy⟩) e h p
    rw [hcons]
    by_cases he : G.IsBridge e
    · have he' : H.IsBridge (f.edgeEquiv ⟨e, h.edge_mem⟩) :=
        (f.isBridge_edgeEquiv_iff ⟨e, h.edge_mem⟩).mpr he
      rw [Walk.toBridgeForest_cons_of_isBridge (f.map_isLink h) _ he',
        Walk.toBridgeForest_cons_of_isBridge h p he,
        f.bridgeForestIso.mapWalk_cons (x := ⟨G.bridgeComponentOf x hx, by simp⟩)
          (y := ⟨G.bridgeComponentOf y h.right_mem, by simp⟩)
          (z := ⟨G.bridgeComponentOf z hy, by simp⟩)]
      exact walk_cons_eq_copy_cons (by simp) (by simp) (by simp) (ih h.right_mem hy)
    · have he' : ¬ H.IsBridge (f.edgeEquiv ⟨e, h.edge_mem⟩) := by
        simpa [f.isBridge_edgeEquiv_iff ⟨e, h.edge_mem⟩] using he
      rw [Walk.toBridgeForest_cons_of_not_isBridge (f.map_isLink h) _ he',
        Walk.toBridgeForest_cons_of_not_isBridge h p he,
        f.bridgeForestIso.mapWalk_copy
          (x := ⟨G.bridgeComponentOf y h.right_mem, by simp⟩)
          (y := ⟨G.bridgeComponentOf z hy, by simp⟩)
          (x' := ⟨G.bridgeComponentOf x hx, by simp⟩)
          (y' := ⟨G.bridgeComponentOf z hy, by simp⟩),
        Walk.copy_copy]
      · simp [ih h.right_mem hy]

/-- Walk transport commutes with projection to the bridge forest. -/
theorem toBridgeForest_mapWalk (f : Iso G H) {x y : V(G)} (p : G.Walk x y) :
    (f.mapWalk p).toBridgeForest (f.vertexEquiv x).property (f.vertexEquiv y).property =
      (f.bridgeForestIso.mapWalk (x := ⟨G.bridgeComponentOf x.val x.property, by simp⟩)
        (y := ⟨G.bridgeComponentOf y.val y.property, by simp⟩)
        (p.toBridgeForest x.property y.property)).copy
          (by simp) (by simp) :=
  toBridgeForest_mapWalk_aux f p x.property y.property

/-- Transporting the lift of a bridge-forest path and projecting back recovers the transported
forest path. -/
theorem toBridgeForest_mapWalk_liftBridgeForest (f : Iso G H)
    {C D : G.BridgeComponent} {x y : α} (q : G.bridgeForest.Walk C D) (hq : q.IsPath)
    (hx : x ∈ V(C.val)) (hy : y ∈ V(D.val)) :
    (f.mapWalk (x := ⟨x, BridgeComponent.mem_vertexSet hx⟩)
      (y := ⟨y, BridgeComponent.mem_vertexSet hy⟩)
      (q.liftBridgeForest hx hy)).toBridgeForest
        (f.vertexEquiv ⟨x, BridgeComponent.mem_vertexSet hx⟩).property
        (f.vertexEquiv ⟨y, BridgeComponent.mem_vertexSet hy⟩).property =
      (f.bridgeForestIso.mapWalk (x := ⟨C, by simp⟩) (y := ⟨D, by simp⟩) q).copy
        (by rw [coe_bridgeForestIso_vertexEquiv_apply, ← f.bridgeComponentEquiv_bridgeComponentOf,
          ← BridgeComponent.eq_bridgeComponentOf hx])
        (by rw [coe_bridgeForestIso_vertexEquiv_apply, ← f.bridgeComponentEquiv_bridgeComponentOf,
          ← BridgeComponent.eq_bridgeComponentOf hy]) := by
  rw [f.toBridgeForest_mapWalk, Walk.toBridgeForest_liftBridgeForest q hq hx hy,
    f.bridgeForestIso.mapWalk_copy (x := ⟨C, by simp⟩) (y := ⟨D, by simp⟩)
      (x' := ⟨G.bridgeComponentOf x (BridgeComponent.mem_vertexSet hx), by simp⟩)
      (y' := ⟨G.bridgeComponentOf y (BridgeComponent.mem_vertexSet hy), by simp⟩),
    Walk.copy_copy]

/-- A multigraph isomorphism respects the correspondence between connected components and connected
components of the bridge forest. -/
theorem connectedComponentEquivBridgeForest_connectedComponentEquiv (f : Iso G H)
    (C : G.ConnectedComponent) :
    H.connectedComponentEquivBridgeForest (f.connectedComponentEquiv C) =
      f.bridgeForestIso.connectedComponentEquiv (G.connectedComponentEquivBridgeForest C) := by
  obtain ⟨x, hx⟩ := C.property.nonempty
  rw [ConnectedComponent.eq_connectedComponentOf hx]
  simp

end Graph.Iso
