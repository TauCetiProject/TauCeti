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

* `Graph.IsLink.eq_leftComponentDeleteEdges_or_eq_rightComponentDeleteEdges`: every component over
  the endpoint component after deleting a linked edge is the component of one of its endpoints.
* `Graph.IsBridge.componentFiberEquivBool`: deleting a bridge splits its original component into
  exactly two components, canonically distinguished by its endpoints.
* `Graph.IsLink.isBridge_iff_nontrivial_componentFiber`: a linked edge is a bridge exactly when
  the fiber of components over its original component is nontrivial.
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
@[expose] public noncomputable def leftComponentDeleteEdges (h : G.IsLink e x y) :
    h.componentFiber :=
  ⟨(G.deleteEdges {e}).connectedComponentOf x (by
    rw [vertexSet_deleteEdges]
    exact h.left_mem), by
    rw [ConnectedComponent.mapOfLE_connectedComponentOf]⟩

/-- The component of the second endpoint after deleting the linked edge, regarded as a component
lying over the original connected component of the first endpoint. -/
@[expose] public noncomputable def rightComponentDeleteEdges (h : G.IsLink e x y) :
    h.componentFiber :=
  ⟨(G.deleteEdges {e}).connectedComponentOf y (by
    rw [vertexSet_deleteEdges]
    exact h.right_mem), by
    rw [ConnectedComponent.mapOfLE_connectedComponentOf]
    exact (G.connectedComponentOf_eq_connectedComponentOf_iff h.right_mem h.left_mem).2
      h.reachable.symm⟩

/-- The underlying left endpoint component after deleting a linked edge. -/
@[simp]
theorem val_leftComponentDeleteEdges (h : G.IsLink e x y) :
    h.leftComponentDeleteEdges.val =
      (G.deleteEdges {e}).connectedComponentOf x (by
        rw [vertexSet_deleteEdges]
        exact h.left_mem) := rfl

/-- The underlying right endpoint component after deleting a linked edge. -/
@[simp]
theorem val_rightComponentDeleteEdges (h : G.IsLink e x y) :
    h.rightComponentDeleteEdges.val =
      (G.deleteEdges {e}).connectedComponentOf y (by
        rw [vertexSet_deleteEdges]
        exact h.right_mem) := rfl

/-- The endpoint components after deleting a linked edge are equal exactly when its endpoints are
still reachable. -/
@[simp]
theorem leftComponentDeleteEdges_eq_rightComponentDeleteEdges_iff (h : G.IsLink e x y) :
    h.leftComponentDeleteEdges = h.rightComponentDeleteEdges ↔
      (G.deleteEdges {e}).Reachable x y := by
  rw [Subtype.ext_iff, val_leftComponentDeleteEdges, val_rightComponentDeleteEdges]
  exact (G.deleteEdges {e}).connectedComponentOf_eq_connectedComponentOf_iff
    (by rw [vertexSet_deleteEdges]; exact h.left_mem)
    (by rw [vertexSet_deleteEdges]; exact h.right_mem)

/-- Membership in the first endpoint component is reachability from that endpoint after deleting
the linked edge. -/
theorem mem_leftComponentDeleteEdges_iff (h : G.IsLink e x y) {z : α} :
    z ∈ V(h.leftComponentDeleteEdges.val.val) ↔
      (G.deleteEdges {e}).Reachable x z := by
  simp [leftComponentDeleteEdges, mem_vertexSet_connectedComponentOf_iff]

/-- Membership in the second endpoint component is reachability from that endpoint after deleting
the linked edge. -/
theorem mem_rightComponentDeleteEdges_iff (h : G.IsLink e x y) {z : α} :
    z ∈ V(h.rightComponentDeleteEdges.val.val) ↔
      (G.deleteEdges {e}).Reachable y z := by
  simp [rightComponentDeleteEdges, mem_vertexSet_connectedComponentOf_iff]

/-- After deleting a linked edge, every component lying over the original endpoint component is
the component of one of the two endpoints. -/
theorem eq_leftComponentDeleteEdges_or_eq_rightComponentDeleteEdges (h : G.IsLink e x y)
    (C : h.componentFiber) :
    C = h.leftComponentDeleteEdges ∨ C = h.rightComponentDeleteEdges := by
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
      (C.val.property.le.vertexSet_mono hzC)
      (by rw [vertexSet_deleteEdges]; exact h.left_mem)).2 hxz.symm
  · right
    apply Subtype.ext
    rw [C.val.eq_connectedComponentOf hzC]
    exact ((G.deleteEdges {e}).connectedComponentOf_eq_connectedComponentOf_iff
      (C.val.property.le.vertexSet_mono hzC)
      (by rw [vertexSet_deleteEdges]; exact h.right_mem)).2 hyz.symm

end IsLink

namespace IsBridge

/-- The two endpoint components obtained by deleting a bridge are distinct. -/
theorem leftComponentDeleteEdges_ne_rightComponentDeleteEdges (he : G.IsBridge e)
    (h : G.IsLink e x y) : h.leftComponentDeleteEdges ≠ h.rightComponentDeleteEdges :=
  mt h.leftComponentDeleteEdges_eq_rightComponentDeleteEdges_iff.mp
    (he.not_reachable_deleteEdges h)

/-- Deleting a bridge splits its original connected component into exactly two components.  The
equivalence sends the component of the first endpoint to `false` and every other component (hence
the component of the second endpoint) to `true`. -/
noncomputable def componentFiberEquivBool (he : G.IsBridge e) (h : G.IsLink e x y) :
    h.componentFiber ≃ Bool := by
  classical
  let side : h.componentFiber → Bool :=
    fun C ↦ if C = h.leftComponentDeleteEdges then false else true
  let endpoint : Bool → h.componentFiber := fun b ↦
    match b with
    | false => h.leftComponentDeleteEdges
    | true => h.rightComponentDeleteEdges
  refine
    { toFun := side
      invFun := endpoint
      left_inv := ?_
      right_inv := ?_ }
  · intro C
    rcases h.eq_leftComponentDeleteEdges_or_eq_rightComponentDeleteEdges C with hC | hC
    · subst C
      simp [side, endpoint]
    · subst C
      simp [side, endpoint, (he.leftComponentDeleteEdges_ne_rightComponentDeleteEdges h).symm]
  · intro b
    cases b <;>
      simp [side, endpoint, (he.leftComponentDeleteEdges_ne_rightComponentDeleteEdges h).symm]

@[simp]
theorem componentFiberEquivBool_leftComponentDeleteEdges (he : G.IsBridge e)
    (h : G.IsLink e x y) :
    he.componentFiberEquivBool h h.leftComponentDeleteEdges = false := by
  simp [componentFiberEquivBool]

@[simp]
theorem componentFiberEquivBool_rightComponentDeleteEdges (he : G.IsBridge e)
    (h : G.IsLink e x y) :
    he.componentFiberEquivBool h h.rightComponentDeleteEdges = true := by
  simp [componentFiberEquivBool, (he.leftComponentDeleteEdges_ne_rightComponentDeleteEdges h).symm]

/-- The inverse of the two-component equivalence sends `false` to the component of the first
endpoint. -/
@[simp]
theorem componentFiberEquivBool_symm_false (he : G.IsBridge e) (h : G.IsLink e x y) :
    (he.componentFiberEquivBool h).symm false = h.leftComponentDeleteEdges := by
  apply (he.componentFiberEquivBool h).injective
  simp

/-- The inverse of the two-component equivalence sends `true` to the component of the second
endpoint. -/
@[simp]
theorem componentFiberEquivBool_symm_true (he : G.IsBridge e) (h : G.IsLink e x y) :
    (he.componentFiberEquivBool h).symm true = h.rightComponentDeleteEdges := by
  apply (he.componentFiberEquivBool h).injective
  simp

/-- Under the two-component equivalence for a bridge, `false` singles out the component of the
first endpoint. -/
@[simp]
theorem componentFiberEquivBool_eq_false_iff (he : G.IsBridge e) (h : G.IsLink e x y)
    (C : h.componentFiber) :
    he.componentFiberEquivBool h C = false ↔ C = h.leftComponentDeleteEdges := by
  rw [← he.componentFiberEquivBool_leftComponentDeleteEdges h]
  exact (he.componentFiberEquivBool h).injective.eq_iff

/-- Under the two-component equivalence for a bridge, `true` singles out the component of the
second endpoint. -/
@[simp]
theorem componentFiberEquivBool_eq_true_iff (he : G.IsBridge e) (h : G.IsLink e x y)
    (C : h.componentFiber) :
    he.componentFiberEquivBool h C = true ↔ C = h.rightComponentDeleteEdges := by
  rw [← he.componentFiberEquivBool_rightComponentDeleteEdges h]
  exact (he.componentFiberEquivBool h).injective.eq_iff

end IsBridge

/-- An edge joining `x` and `y` is a bridge exactly when the fiber of components over its original
connected component is nontrivial. -/
theorem IsLink.isBridge_iff_nontrivial_componentFiber (h : G.IsLink e x y) :
    G.IsBridge e ↔ Nontrivial h.componentFiber := by
  constructor
  · intro he
    exact ⟨⟨h.leftComponentDeleteEdges, h.rightComponentDeleteEdges,
      he.leftComponentDeleteEdges_ne_rightComponentDeleteEdges h⟩⟩
  · intro hnontrivial
    rw [h.isBridge_iff_not_reachable_deleteEdges]
    intro hxy
    have hend := h.leftComponentDeleteEdges_eq_rightComponentDeleteEdges_iff.mpr hxy
    obtain ⟨C, D, hCD⟩ := hnontrivial.exists_pair_ne
    apply hCD
    have hall (A : h.componentFiber) : A = h.leftComponentDeleteEdges := by
      rcases h.eq_leftComponentDeleteEdges_or_eq_rightComponentDeleteEdges A with hA | hA
      · exact hA
      · exact hA.trans hend.symm
    exact (hall C).trans (hall D).symm

/-- An edge joining `x` and `y` is a bridge exactly when deleting it splits its original connected
component into exactly two components. -/
theorem IsLink.isBridge_iff_nonempty_componentFiber_equiv_bool (h : G.IsLink e x y) :
    G.IsBridge e ↔ Nonempty (h.componentFiber ≃ Bool) := by
  constructor
  · exact fun he ↦ ⟨he.componentFiberEquivBool h⟩
  · rintro ⟨f⟩
    rw [h.isBridge_iff_nontrivial_componentFiber]
    exact f.symm.injective.nontrivial

end Graph
