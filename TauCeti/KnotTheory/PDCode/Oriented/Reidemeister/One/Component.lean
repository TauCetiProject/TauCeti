/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.One.Basic

/-!
# Component transport across an arc first Reidemeister move

`OrientedPDCode.reidemeisterOneComponentEquiv` tracks individual link components when
inserting a kink into an arc. Every old half-edge stays on its original component,
all four slots of the kink belong to the component of the cut arc, and each
crossing-free circle keeps its label. Both orientations of the cut arc and both
over-strand choices are included. Planarity is not needed for this correspondence.

The construction collapses the new kink to its cut arc on outgoing traversal
classes. The native component-count theorem proves that this explicit surjective
collapse is a bijection. The inverse is the component transport for kink insertion;
its identity and inverse-composition laws are the native `Equiv` laws.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1
  (the first Reidemeister move).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3
  (oriented component traversal).
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open Equiv Equiv.Perm PDCode

variable {n : ℕ} (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool)

private def collapseHalfEdge (x : Fin (4 * (n + 1))) : D.CrossingComponent :=
  Sum.elim D.crossingComponentOfHalfEdge (fun _ ↦ D.crossingComponentOfHalfEdge h)
    ((halfEdgeSuccEquiv n).symm x)

private theorem collapseHalfEdge_crossingTurn (x : Fin (4 * (n + 1))) :
    collapseHalfEdge D h ((D.reidemeisterOne h b).crossingTurn x) =
      collapseHalfEdge D h x := by
  obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x <;>
    simp [collapseHalfEdge, crossingTurn_eq_permCongr_sumCongr
      (D.toPDCode.reidemeisterOne_halfEdge h b), Equiv.permCongr_apply]

private theorem collapseHalfEdge_edgePair (x : Fin (4 * (n + 1))) :
    collapseHalfEdge D h ((D.reidemeisterOne h b).edgePair.val x) =
      collapseHalfEdge D h x := by
  obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
  · by_cases hx : x = h
    · subst x
      simp [collapseHalfEdge]
    · by_cases hx' : x = D.edgePair.val h
      · subst x
        simp [collapseHalfEdge]
      · simp [collapseHalfEdge, PDCode.reidemeisterOne_edgePair_inl_of_ne, hx, hx']
  · fin_cases s <;> simp [collapseHalfEdge]

private theorem collapseHalfEdge_componentPermOutgoing
    (x : {x : Fin (4 * (n + 1)) // (D.reidemeisterOne h b).orientation x = true}) :
    collapseHalfEdge D h ((D.reidemeisterOne h b).componentPermOutgoing x) =
      collapseHalfEdge D h x := by
  simp only [componentPermOutgoing_apply, PDCode.componentPerm_apply]
  rw [collapseHalfEdge_crossingTurn, collapseHalfEdge_edgePair]

private def collapseCrossingComponent : (D.reidemeisterOne h b).CrossingComponent →
    D.CrossingComponent :=
  Quotient.lift (fun x ↦ collapseHalfEdge D h x.val) fun _ _ hxy ↦
    hxy.apply_eq_of_apply_eq (f := fun x ↦ collapseHalfEdge D h x.val)
      (collapseHalfEdge_componentPermOutgoing D h b)

private theorem collapseCrossingComponent_halfEdge (x : Fin (4 * (n + 1))) :
    collapseCrossingComponent D h b ((D.reidemeisterOne h b).crossingComponentOfHalfEdge x) =
      collapseHalfEdge D h x := by
  cases hx : (D.reidemeisterOne h b).orientation x with
  | true => rw [crossingComponentOfHalfEdge_of_outgoing _ x hx]; rfl
  | false =>
    rw [crossingComponentOfHalfEdge_of_incoming _ x hx]
    exact collapseHalfEdge_edgePair D h b x

private theorem collapseCrossingComponent_surjective :
    Function.Surjective (collapseCrossingComponent D h b) := by
  intro c
  obtain ⟨⟨x, hx⟩, rfl⟩ := Quotient.mk_surjective c
  refine ⟨(D.reidemeisterOne h b).crossingComponentOfHalfEdge
    (halfEdgeSuccEquiv n (.inl x)), ?_⟩
  rw [collapseCrossingComponent_halfEdge]
  simpa [collapseHalfEdge] using D.crossingComponentOfHalfEdge_of_outgoing x hx

private def collapseCrossingComponentEquiv :
    (D.reidemeisterOne h b).CrossingComponent ≃ D.CrossingComponent :=
  Equiv.ofBijective (collapseCrossingComponent D h b)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨collapseCrossingComponent_surjective D h b, by simp⟩)

/-- Inserting a kink into an arc transports every old component by inclusion and
keeps the individual crossing-free labels fixed. Its inverse collapses the kink
into the component containing the cut arc. -/
def reidemeisterOneComponentEquiv : D.Component ≃ (D.reidemeisterOne h b).Component :=
  Equiv.sumCongr (collapseCrossingComponentEquiv D h b).symm (finCongr (by simp))

/-- Under kink removal, every old half-edge recovers its original component. -/
@[simp] theorem reidemeisterOneComponentEquiv_symm_inl_halfEdge (x : Fin (4 * n)) :
    (D.reidemeisterOneComponentEquiv h b).symm
        (.inl ((D.reidemeisterOne h b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv n (.inl x)))) =
      .inl (D.crossingComponentOfHalfEdge x) := by
  simp [reidemeisterOneComponentEquiv, collapseCrossingComponentEquiv,
    collapseCrossingComponent_halfEdge, collapseHalfEdge]

/-- Inserting a kink preserves the component represented by each old half-edge,
including incoming half-edges. -/
@[simp] theorem reidemeisterOneComponentEquiv_inl_halfEdge (x : Fin (4 * n)) :
    D.reidemeisterOneComponentEquiv h b (.inl (D.crossingComponentOfHalfEdge x)) =
      .inl ((D.reidemeisterOne h b).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv n (.inl x))) := by
  apply (D.reidemeisterOneComponentEquiv h b).symm.injective
  simp

/-- An old outgoing representative is transported to its included half-edge. -/
@[simp] theorem reidemeisterOneComponentEquiv_componentOfOutgoing
    (x : {x : Fin (4 * n) // D.orientation x = true}) :
    D.reidemeisterOneComponentEquiv h b (D.componentOfOutgoing x) =
      (D.reidemeisterOne h b).componentOfOutgoing
        ⟨halfEdgeSuccEquiv n (.inl x.val), by simpa using x.property⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.reidemeisterOneComponentEquiv_inl_halfEdge h b x.val

/-- Every slot of the new kink belongs to the component of the cut arc. -/
@[simp] theorem reidemeisterOneComponentEquiv_symm_inl_new (s : Fin 4) :
    (D.reidemeisterOneComponentEquiv h b).symm
        (.inl ((D.reidemeisterOne h b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv n (.inr s)))) =
      .inl (D.crossingComponentOfHalfEdge h) := by
  simp [reidemeisterOneComponentEquiv, collapseCrossingComponentEquiv,
    collapseCrossingComponent_halfEdge, collapseHalfEdge]

/-- Inserting a kink preserves each labelled crossing-free component. -/
@[simp] theorem reidemeisterOneComponentEquiv_inr (i : Fin D.crossinglessComponentCount) :
    D.reidemeisterOneComponentEquiv h b (.inr i) = .inr (finCongr (by simp) i) := (rfl)

/-- Removing a kink preserves each labelled crossing-free component. -/
@[simp] theorem reidemeisterOneComponentEquiv_symm_inr
    (i : Fin (D.reidemeisterOne h b).crossinglessComponentCount) :
    (D.reidemeisterOneComponentEquiv h b).symm (.inr i) = .inr (finCongr (by simp) i) := (rfl)

end TauCeti.OrientedPDCode
