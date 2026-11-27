/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic

/-!
# The components split by a bridge

Deleting an edge can only split the connected component containing its endpoints.  Within that
component, every new component contains one of the two endpoints.  If the edge is a bridge these
endpoint components are distinct, so they are exactly the two components into which the original
component splits.  Conversely, if deletion produces two components over the original endpoint
component, the edge is a bridge.

The components lying over an original component are expressed as the fiber of
`Graph.ConnectedComponent.mapOfLE` for `G.deleteEdges {e} ≤ G`.  This keeps the statement local to
the component containing the edge and makes no finiteness assumption on the graph.

## Main results

* `Graph.IsLink.componentFiber_eq_source_or_target`: every component over the endpoint component
  after deleting a linked edge is the component of one of its endpoints.
* `Graph.IsBridge.componentFiberEquivBool`: deleting a bridge splits its original component into
  exactly two components, canonically distinguished by its endpoints.
* `Graph.IsLink.isBridge_iff_nonempty_componentFiber_equiv_bool`: a linked edge is a bridge exactly
  when the fiber of components over its original component has two elements.

## References

* R. Diestel, *Graph Theory*, 6th edition, Section 1.4.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {e : β} {x y : α}

namespace IsLink

/-- The connected components left over the original endpoint component after deleting a linked
edge. -/
abbrev componentFiber (h : G.IsLink e x y) :=
  {C : (G.deleteEdges {e}).ConnectedComponent //
    ConnectedComponent.mapOfLE (deleteEdges_le : G.deleteEdges {e} ≤ G) C =
      G.connectedComponentOf x h.left_mem}

/-- The component of the first endpoint after deleting the linked edge, regarded as a component
lying over its original connected component. -/
noncomputable def sourceComponentAfterDelete (h : G.IsLink e x y) : h.componentFiber :=
  ⟨(G.deleteEdges {e}).connectedComponentOf x (by simpa using h.left_mem), by
    rw [ConnectedComponent.mapOfLE_connectedComponentOf]⟩

/-- The component of the second endpoint after deleting the linked edge, regarded as a component
lying over the original connected component of the first endpoint. -/
noncomputable def targetComponentAfterDelete (h : G.IsLink e x y) : h.componentFiber :=
  ⟨(G.deleteEdges {e}).connectedComponentOf y (by simpa using h.right_mem), by
    rw [ConnectedComponent.mapOfLE_connectedComponentOf]
    exact (G.connectedComponentOf_eq_connectedComponentOf_iff h.right_mem h.left_mem).2
      h.reachable.symm⟩

/-- Membership in the first endpoint component is reachability from that endpoint after deleting
the linked edge. -/
@[simp]
theorem mem_sourceComponentAfterDelete_iff (h : G.IsLink e x y) {z : α} :
    z ∈ V(h.sourceComponentAfterDelete.val.val) ↔
      (G.deleteEdges {e}).Reachable x z := by
  simp [sourceComponentAfterDelete, mem_vertexSet_connectedComponentOf_iff]

/-- Membership in the second endpoint component is reachability from that endpoint after deleting
the linked edge. -/
@[simp]
theorem mem_targetComponentAfterDelete_iff (h : G.IsLink e x y) {z : α} :
    z ∈ V(h.targetComponentAfterDelete.val.val) ↔
      (G.deleteEdges {e}).Reachable y z := by
  simp [targetComponentAfterDelete, mem_vertexSet_connectedComponentOf_iff]

/-- After deleting a linked edge, every component lying over the original endpoint component is
the component of one of the two endpoints. -/
theorem componentFiber_eq_source_or_target (h : G.IsLink e x y)
    (C : h.componentFiber) :
    C = h.sourceComponentAfterDelete ∨ C = h.targetComponentAfterDelete := by
  obtain ⟨z, hzC⟩ := C.val.property.nonempty
  have hxz : G.Reachable x z := by
    rw [← mem_vertexSet_connectedComponentOf_iff h.left_mem]
    rw [← C.property]
    exact C.val.mem_vertexSet_mapOfLE (deleteEdges_le : G.deleteEdges {e} ≤ G) hzC
  rcases h.reachable_iff_reachable_deleteEdges_or.1 hxz with hxz | hyz
  · left
    apply Subtype.ext
    rw [C.val.eq_connectedComponentOf hzC]
    exact ((G.deleteEdges {e}).connectedComponentOf_eq_connectedComponentOf_iff
      (C.val.property.le.vertexSet_mono hzC) (by simpa using h.left_mem)).2 hxz.symm
  · right
    apply Subtype.ext
    rw [C.val.eq_connectedComponentOf hzC]
    exact ((G.deleteEdges {e}).connectedComponentOf_eq_connectedComponentOf_iff
      (C.val.property.le.vertexSet_mono hzC) (by simpa using h.right_mem)).2 hyz.symm

end IsLink

namespace IsBridge

/-- The two endpoint components obtained by deleting a bridge are distinct. -/
theorem sourceComponentAfterDelete_ne_target (he : G.IsBridge e) (h : G.IsLink e x y) :
    h.sourceComponentAfterDelete ≠ h.targetComponentAfterDelete := by
  intro hxy
  have hval := congrArg Subtype.val hxy
  have : (G.deleteEdges {e}).Reachable x y := by
    rw [← (G.deleteEdges {e}).connectedComponentOf_eq_connectedComponentOf_iff
      (by simpa using h.left_mem) (by simpa using h.right_mem)]
    simpa [IsLink.sourceComponentAfterDelete, IsLink.targetComponentAfterDelete] using hval
  exact he.not_reachable_deleteEdges h this

/-- Deleting a bridge splits its original connected component into exactly two components.  The
equivalence sends the component of the first endpoint to `false` and every other component (hence
the component of the second endpoint) to `true`. -/
noncomputable def componentFiberEquivBool (he : G.IsBridge e) (h : G.IsLink e x y) :
    h.componentFiber ≃ Bool := by
  classical
  let side : h.componentFiber → Bool :=
    fun C ↦ if C = h.sourceComponentAfterDelete then false else true
  exact Equiv.ofBijective side
    ⟨by
      intro C D hCD
      have hne := he.sourceComponentAfterDelete_ne_target h
      rcases h.componentFiber_eq_source_or_target C with hC | hC
      · rcases h.componentFiber_eq_source_or_target D with hD | hD
        · exact hC.trans hD.symm
        · exfalso
          subst C
          subst D
          simp [side, hne.symm] at hCD
      · rcases h.componentFiber_eq_source_or_target D with hD | hD
        · exfalso
          subst C
          subst D
          simp [side, hne.symm] at hCD
        · exact hC.trans hD.symm,
    by
      intro b
      cases b
      · exact ⟨h.sourceComponentAfterDelete, by simp [side]⟩
      · exact ⟨h.targetComponentAfterDelete, by
          simp [side, (he.sourceComponentAfterDelete_ne_target h).symm]⟩⟩

@[simp]
theorem componentFiberEquivBool_source (he : G.IsBridge e) (h : G.IsLink e x y) :
    he.componentFiberEquivBool h h.sourceComponentAfterDelete = false := by
  simp [componentFiberEquivBool]

@[simp]
theorem componentFiberEquivBool_target (he : G.IsBridge e) (h : G.IsLink e x y) :
    he.componentFiberEquivBool h h.targetComponentAfterDelete = true := by
  simp [componentFiberEquivBool, (he.sourceComponentAfterDelete_ne_target h).symm]

/-- Under the two-component equivalence for a bridge, `false` singles out the component of the
first endpoint. -/
@[simp]
theorem componentFiberEquivBool_eq_false_iff (he : G.IsBridge e) (h : G.IsLink e x y)
    (C : h.componentFiber) :
    he.componentFiberEquivBool h C = false ↔ C = h.sourceComponentAfterDelete := by
  rw [← he.componentFiberEquivBool_source h]
  exact (he.componentFiberEquivBool h).injective.eq_iff

/-- Under the two-component equivalence for a bridge, `true` singles out the component of the
second endpoint. -/
@[simp]
theorem componentFiberEquivBool_eq_true_iff (he : G.IsBridge e) (h : G.IsLink e x y)
    (C : h.componentFiber) :
    he.componentFiberEquivBool h C = true ↔ C = h.targetComponentAfterDelete := by
  rw [← he.componentFiberEquivBool_target h]
  exact (he.componentFiberEquivBool h).injective.eq_iff

end IsBridge

/-- An edge joining `x` and `y` is a bridge exactly when deleting it splits its original connected
component into exactly two components. -/
theorem IsLink.isBridge_iff_nonempty_componentFiber_equiv_bool (h : G.IsLink e x y) :
    G.IsBridge e ↔ Nonempty (h.componentFiber ≃ Bool) := by
  constructor
  · exact fun he ↦ ⟨he.componentFiberEquivBool h⟩
  · rintro ⟨f⟩
    rw [h.isBridge_iff_not_reachable_deleteEdges]
    intro hxy
    have hend : h.sourceComponentAfterDelete = h.targetComponentAfterDelete := by
      apply Subtype.ext
      exact ((G.deleteEdges {e}).connectedComponentOf_eq_connectedComponentOf_iff
        (by simpa using h.left_mem) (by simpa using h.right_mem)).2 hxy
    have hall (C : h.componentFiber) : C = h.sourceComponentAfterDelete := by
      rcases h.componentFiber_eq_source_or_target C with hC | hC
      · exact hC
      · exact hC.trans hend.symm
    have hs : f.symm false = f.symm true := (hall _).trans (hall _).symm
    exact Bool.false_ne_true (by simpa using congrArg f hs)

end Graph
