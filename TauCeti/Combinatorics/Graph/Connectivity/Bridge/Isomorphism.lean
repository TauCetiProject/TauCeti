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

`Graph.Iso.bridgeComponentEquiv`, `Graph.Iso.bridgeComponentIso`, and `Graph.Iso.bridgeForestIso`
respect identity, inversion, and composition. Furthermore, `Graph.Iso.bridgeForestIso` commutes
with walk projection (`Graph.Walk.toBridgeForest`) and with the component correspondence
`Graph.connectedComponentEquivBridgeForest`. No finiteness hypotheses are required.
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

/-- A multigraph isomorphism induces an equivalence of bridge components. -/
noncomputable def bridgeComponentEquiv (f : Iso G H) :
    G.BridgeComponent ≃ H.BridgeComponent :=
  f.deleteEdgesBridgeSetIso.connectedComponentEquiv

/-- The bridge component of an actual vertex is sent to the bridge component of its image. -/
@[simp]
theorem bridgeComponentEquiv_bridgeComponentOf (f : Iso G H) {x : α} (hx : x ∈ V(G)) :
    f.bridgeComponentEquiv (G.bridgeComponentOf x hx) =
      H.bridgeComponentOf (f.vertexEquiv ⟨x, hx⟩) (f.vertexEquiv ⟨x, hx⟩).property := by
  rw [bridgeComponentEquiv, bridgeComponentOf_def, bridgeComponentOf_def,
    f.deleteEdgesBridgeSetIso.connectedComponentEquiv_connectedComponentOf]
  simp only [deleteEdgesBridgeSetIso, coe_deleteEdgesIso_vertexEquiv_apply]

/-- The inverse bridge-component equivalence sends the component of an actual vertex to the
component of its preimage. -/
@[simp]
theorem bridgeComponentEquiv_symm_bridgeComponentOf (f : Iso G H) {y : α'} (hy : y ∈ V(H)) :
    f.bridgeComponentEquiv.symm (H.bridgeComponentOf y hy) =
      G.bridgeComponentOf (f.vertexEquiv.symm ⟨y, hy⟩)
        (f.vertexEquiv.symm ⟨y, hy⟩).property := by
  rw [bridgeComponentEquiv, bridgeComponentOf_def, bridgeComponentOf_def,
    f.deleteEdgesBridgeSetIso.connectedComponentEquiv_symm_connectedComponentOf]
  simp only [deleteEdgesBridgeSetIso, coe_deleteEdgesIso_vertexEquiv_symm_apply]

/-- The vertices of a transported bridge component are the transported vertices of the component. -/
theorem vertexSet_bridgeComponentEquiv (f : Iso G H) (C : G.BridgeComponent) :
    V((f.bridgeComponentEquiv C).val) = f.mapVertexSet V(C.val) := by
  simpa [bridgeComponentEquiv, deleteEdgesBridgeSetIso] using
    f.deleteEdgesBridgeSetIso.vertexSet_connectedComponentEquiv C

/-- The edges of a transported bridge component are the transported edges of the component. -/
theorem edgeSet_bridgeComponentEquiv (f : Iso G H) (C : G.BridgeComponent) :
    E((f.bridgeComponentEquiv C).val) = f.mapEdgeSet E(C.val) := by
  rw [bridgeComponentEquiv, edgeSet_connectedComponentEquiv, deleteEdgesBridgeSetIso,
    mapEdgeSet_deleteEdgesIso, sdiff_eq_left, disjoint_left]
  intro e he heH
  have he' := f.mapEdgeSet_subset_edgeSet E(C.val) he
  have hC : (f.edgeEquiv.symm ⟨e, he'⟩ : β) ∈ E(C.val) :=
    (f.mem_mapEdgeSet_iff E(C.val) ⟨e, he'⟩).mp he
  have hG := C.property.le.edgeSet_mono hC
  rw [edgeSet_deleteEdges, mem_sdiff] at hG
  exact hG.2 (mem_bridgeSet.mpr ((f.isBridge_edgeEquiv_iff _).mp
    (by simpa [mem_bridgeSet] using heH)))

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
  rw [edgeSet_bridgeComponentEquiv, f.mem_mapEdgeSet_iff]
  simp

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

/-- The identity isomorphism acts identically on bridge components. -/
@[simp]
theorem bridgeComponentEquiv_refl (G : Graph α β) :
    (refl G).bridgeComponentEquiv = Equiv.refl G.BridgeComponent := by
  simp [bridgeComponentEquiv, deleteEdgesBridgeSetIso]

/-- Inversion of multigraph isomorphisms inverts the induced bridge-component equivalence. -/
@[simp]
theorem bridgeComponentEquiv_symm (f : Iso G H) :
    f.symm.bridgeComponentEquiv = f.bridgeComponentEquiv.symm := by
  rw [bridgeComponentEquiv, bridgeComponentEquiv, deleteEdgesBridgeSetIso,
    deleteEdgesBridgeSetIso, ← connectedComponentEquiv_symm]
  congr 1
  exact (deleteEdgesIso_symm f _).symm

/-- Composition of multigraph isomorphisms composes their bridge-component equivalences. -/
@[simp]
theorem bridgeComponentEquiv_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).bridgeComponentEquiv = f.bridgeComponentEquiv.trans g.bridgeComponentEquiv := by
  rw [bridgeComponentEquiv, bridgeComponentEquiv, bridgeComponentEquiv,
    deleteEdgesBridgeSetIso, deleteEdgesBridgeSetIso, deleteEdgesBridgeSetIso,
    ← connectedComponentEquiv_trans]
  congr 1
  exact (deleteEdgesIso_trans f g _ _).symm

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

private theorem bridgeComponentIso_cast_eq {G₁ : Graph α β} {G₂ : Graph α' β'}
    {C₁ : G₁.BridgeComponent} {D₁ D₂ : G₂.BridgeComponent} (h : D₁ = D₂)
    (k₁ : Iso C₁.val D₂.val) (k₂ : Iso C₁.val D₁.val)
    (hv : ∀ x : V(C₁.val), (k₁.vertexEquiv x : α') = (k₂.vertexEquiv x : α'))
    (he : ∀ e : E(C₁.val), (k₁.edgeEquiv e : β') = (k₂.edgeEquiv e : β')) :
    k₁ = (congrArg Subtype.val h) ▸ k₂ := by
  subst h
  ext x
  · exact hv x
  · exact he x

/-- Restricting the identity isomorphism to a bridge component gives the identity isomorphism,
identifying the target component. -/
@[simp]
theorem bridgeComponentIso_refl (G : Graph α β) (C : G.BridgeComponent) :
    (refl G).bridgeComponentIso C =
      (congrArg Subtype.val (by simp : C = (refl G).bridgeComponentEquiv C)) ▸ refl C.val :=
  bridgeComponentIso_cast_eq (by simp) _ _ (fun x ↦ by simp) (fun e ↦ by simp)

/-- Restricting an inverse isomorphism to the transported bridge component equals the inverse of
the restricted isomorphism, identifying the target component. -/
@[simp]
theorem bridgeComponentIso_symm (f : Iso G H) (C : G.BridgeComponent) :
    (f.bridgeComponentIso C).symm =
      (congrArg Subtype.val
        (by simp : f.symm.bridgeComponentEquiv (f.bridgeComponentEquiv C) = C)) ▸
        f.symm.bridgeComponentIso (f.bridgeComponentEquiv C) :=
  bridgeComponentIso_cast_eq (by simp) _ _ (fun y ↦ by simp) (fun e ↦ by simp)

/-- Restricting a composite isomorphism to a bridge component equals the composite of the
restricted isomorphisms, identifying the target component. -/
@[simp]
theorem bridgeComponentIso_trans (f : Iso G H) (g : Iso H K) (C : G.BridgeComponent) :
    (f.trans g).bridgeComponentIso C =
      (congrArg Subtype.val
        (by simp : g.bridgeComponentEquiv (f.bridgeComponentEquiv C) =
          (f.trans g).bridgeComponentEquiv C)) ▸
        (f.bridgeComponentIso C).trans
          (g.bridgeComponentIso (f.bridgeComponentEquiv C)) :=
  bridgeComponentIso_cast_eq (by simp) _ _ (fun x ↦ by simp) (fun e ↦ by simp)

/-! ### The bridge forest -/

/-- A multigraph isomorphism induces an isomorphism between the bridge forests. -/
noncomputable def bridgeForestIso (f : Iso G H) : Iso G.bridgeForest H.bridgeForest where
  vertexEquiv := f.bridgeComponentEquiv.subtypeEquiv fun _ ↦ by simp
  edgeEquiv :=
    (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ E(G))) (q := (· ∈ E(G.bridgeForest)))
      (fun {_} he ↦ G.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset he))).symm.trans
      ((f.edgeEquiv.subtypeEquiv (p := fun e : E(G) ↦ (e : β) ∈ E(G.bridgeForest))
        (q := fun e : E(H) ↦ (e : β') ∈ E(H.bridgeForest)) fun e ↦ by
          simpa [edgeSet_bridgeForest, mem_bridgeSet] using (f.isBridge_edgeEquiv_iff e).symm).trans
        (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ E(H))) (q := (· ∈ E(H.bridgeForest)))
          (fun {_} he ↦ H.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset he))))
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
        simp only [Equiv.apply_symm_apply]
        simp only [Equiv.trans_apply, Equiv.subtypeSubtypeEquivSubtype_apply_coe,
          Equiv.subtypeEquiv_apply] at hl
        have heq : (↑((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ E(G)))
            (q := (· ∈ E(G.bridgeForest)))
            (fun {_} he ↦ G.bridgeSet_subset_edgeSet (edgeSet_bridgeForest.subset he))).symm e) :
            E(G)) = e' := by
          ext
          simp [e']
        rwa [heq] at hl
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
    rw [f.mapWalk_cons (x := ⟨x, hx⟩) (y := ⟨y, h.right_mem⟩) (z := ⟨z, hy⟩) e h p]
    by_cases he : G.IsBridge e
    · have he' : H.IsBridge (f.edgeEquiv ⟨e, h.edge_mem⟩) :=
        (f.isBridge_edgeEquiv_iff ⟨e, h.edge_mem⟩).mpr he
      rw [Walk.toBridgeForest_cons_of_isBridge (f.map_isLink h) _ he',
        Walk.toBridgeForest_cons_of_isBridge h p he,
        f.bridgeForestIso.mapWalk_cons (x := ⟨G.bridgeComponentOf x hx, by simp⟩)
          (y := ⟨G.bridgeComponentOf y h.right_mem, by simp⟩)
          (z := ⟨G.bridgeComponentOf z hy, by simp⟩)]
      exact Walk.cons_eq_copy_cons (by simp) (by simp) (by simp) (ih h.right_mem hy)
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
      simp [ih h.right_mem hy]

/-- Walk transport commutes with projection to the bridge forest. -/
@[simp]
theorem toBridgeForest_mapWalk (f : Iso G H) {x y : V(G)} (p : G.Walk x y) :
    (f.mapWalk p).toBridgeForest (f.vertexEquiv x).property (f.vertexEquiv y).property =
      (f.bridgeForestIso.mapWalk (x := ⟨G.bridgeComponentOf x.val x.property, by simp⟩)
        (y := ⟨G.bridgeComponentOf y.val y.property, by simp⟩)
        (p.toBridgeForest x.property y.property)).copy
          (by simp) (by simp) :=
  toBridgeForest_mapWalk_aux f p x.property y.property

/-- A multigraph isomorphism respects the correspondence between connected components and connected
components of the bridge forest. -/
@[simp]
theorem connectedComponentEquivBridgeForest_connectedComponentEquiv (f : Iso G H)
    (C : G.ConnectedComponent) :
    H.connectedComponentEquivBridgeForest (f.connectedComponentEquiv C) =
      f.bridgeForestIso.connectedComponentEquiv (G.connectedComponentEquivBridgeForest C) := by
  obtain ⟨x, hx⟩ := C.property.nonempty
  rw [ConnectedComponent.eq_connectedComponentOf hx]
  simp only [connectedComponentEquiv_connectedComponentOf,
    connectedComponentEquivBridgeForest_connectedComponentOf,
    coe_bridgeForestIso_vertexEquiv_apply, bridgeComponentEquiv_bridgeComponentOf]

end Graph.Iso
