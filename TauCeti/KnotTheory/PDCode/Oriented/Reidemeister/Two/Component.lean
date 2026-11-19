/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.Oriented.ClaspInsertion
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Circles

/-!
# Component transport across second Reidemeister moves

The three native forms of the second Reidemeister move each come with a bijection of labelled
link components, not just an equality of component counts.

* `OrientedPDCode.insertClaspComponentEquiv`: a clasp between two distinct arcs. Every old
  half-edge stays on its component, and each slot of the two new crossings belongs to the
  component of the arc routed through it. Crossing-free labels are kept.
* `OrientedPDCode.insertCircleClaspComponentEquiv`: a clasp between an arc and a crossing-free
  circle. The circle with the last crossing-free label becomes the crossing-bearing component
  through the circle slots of the clasp; the other labels and old components are kept.
* `OrientedPDCode.adjoinTwoCircleClaspComponentEquiv`: a clasp between two crossing-free
  circles, adjoined as a disjoint union. The last two crossing-free labels become the two
  components of the clasp, in their order of adjunction.

Each transport is constructed in the removing direction, by sending every half-edge of the new
code to the component of the old code it lies on. This map is constant along arcs and through
crossings, so it descends to components (`OrientedPDCode.CrossingComponent.lift`). It is
surjective, and the native component-count theorems show that it is a bijection. Planarity and
the face condition of the move are not needed for these correspondences.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1
  (the second Reidemeister move).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3
  (oriented component traversal).
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open Equiv PDCode

variable {n : ℕ}

/-! ### A clasp between two arcs -/

section InsertClasp

variable (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
  (hqe : q ≠ D.edgePair.val p)

/-- The component of the old code containing a half-edge of the clasp insertion. The slots of
the first new crossing alternate between the arcs at `p` and `q`, and those of the second
between the arcs at `q` and `p`. -/
private def claspCollapse (x : Fin (4 * (n + 2))) : D.CrossingComponent :=
  Sum.elim
    (fun y ↦ Sum.elim D.crossingComponentOfHalfEdge
      (fun s ↦ D.crossingComponentOfHalfEdge (![p, q, p, q] s)) ((halfEdgeSuccEquiv n).symm y))
    (fun s ↦ D.crossingComponentOfHalfEdge (![q, p, q, p] s))
    ((halfEdgeSuccEquiv (n + 1)).symm x)

private theorem claspCollapse_crossingTurn (x : Fin (4 * (n + 2))) :
    claspCollapse D p q ((D.insertClasp p q b hqp hqe).crossingTurn x) =
      claspCollapse D p q x := by
  obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
  · obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    · simp [claspCollapse]
    · fin_cases s <;> simp [claspCollapse, oppositeCrossingSlot_apply]
  · fin_cases s <;> simp [claspCollapse, oppositeCrossingSlot_apply]

private theorem claspCollapse_edgePair (x : Fin (4 * (n + 2))) :
    claspCollapse D p q ((D.insertClasp p q b hqp hqe).edgePair.val x) =
      claspCollapse D p q x := by
  obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
  · obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    · by_cases hxp : x = p
      · subst x
        simp [claspCollapse]
      by_cases hxe : x = D.edgePair.val p
      · subst x
        simp [claspCollapse]
      by_cases hxq : x = q
      · subst x
        simp [claspCollapse]
      by_cases hxe' : x = D.edgePair.val q
      · subst x
        simp [claspCollapse]
      simp [claspCollapse, insertClasp_edgePair_inl_inl_of_ne _ p q b hqp hqe hxp hxe hxq hxe']
    · fin_cases s <;> simp [claspCollapse]
  · fin_cases s <;> simp [claspCollapse]

private def claspCollapseComponent :
    (D.insertClasp p q b hqp hqe).CrossingComponent → D.CrossingComponent :=
  CrossingComponent.lift (claspCollapse D p q) (claspCollapse_crossingTurn D p q b hqp hqe)
    (claspCollapse_edgePair D p q b hqp hqe)

private theorem claspCollapseComponent_halfEdge (x : Fin (4 * (n + 2))) :
    claspCollapseComponent D p q b hqp hqe
        ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge x) =
      claspCollapse D p q x :=
  CrossingComponent.lift_crossingComponentOfHalfEdge _ _ _ x

private theorem claspCollapseComponent_surjective :
    Function.Surjective (claspCollapseComponent D p q b hqp hqe) := by
  intro c
  obtain ⟨⟨x, hx⟩, rfl⟩ := Quotient.mk_surjective c
  refine ⟨(D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))), ?_⟩
  rw [claspCollapseComponent_halfEdge]
  simpa [claspCollapse] using D.crossingComponentOfHalfEdge_of_outgoing x hx

private def claspCollapseComponentEquiv :
    (D.insertClasp p q b hqp hqe).CrossingComponent ≃ D.CrossingComponent :=
  Equiv.ofBijective (claspCollapseComponent D p q b hqp hqe)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨claspCollapseComponent_surjective D p q b hqp hqe, by simp⟩)

/-- Inserting a clasp between two distinct arcs transports every old component by inclusion
and keeps the individual crossing-free labels fixed. Its inverse sends each slot of the clasp
to the component of the arc routed through it. -/
def insertClaspComponentEquiv : D.Component ≃ (D.insertClasp p q b hqp hqe).Component :=
  Equiv.sumCongr (claspCollapseComponentEquiv D p q b hqp hqe).symm (finCongr (by simp))

/-- Under clasp removal, every old half-edge recovers its original component. -/
@[simp] theorem insertClaspComponentEquiv_symm_inl_halfEdge (x : Fin (4 * n)) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        (.inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))))) =
      .inl (D.crossingComponentOfHalfEdge x) := by
  simp [insertClaspComponentEquiv, claspCollapseComponentEquiv,
    claspCollapseComponent_halfEdge, claspCollapse]

/-- Inserting a clasp preserves the component represented by each old half-edge, including
incoming half-edges. -/
@[simp] theorem insertClaspComponentEquiv_inl_halfEdge (x : Fin (4 * n)) :
    D.insertClaspComponentEquiv p q b hqp hqe (.inl (D.crossingComponentOfHalfEdge x)) =
      .inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))))) := by
  apply (D.insertClaspComponentEquiv p q b hqp hqe).symm.injective
  simp

/-- An old outgoing representative is transported to its included half-edge. -/
@[simp] theorem insertClaspComponentEquiv_componentOfOutgoing
    (x : {x : Fin (4 * n) // D.orientation x = true}) :
    D.insertClaspComponentEquiv p q b hqp hqe (D.componentOfOutgoing x) =
      (D.insertClasp p q b hqp hqe).componentOfOutgoing
        ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x.val))),
          by simpa using x.property⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertClaspComponentEquiv_inl_halfEdge p q b hqp hqe x.val

/-- Slots `0` and `2` of the first new crossing lie on the component of the arc at `p`, slots
`1` and `3` on that of the arc at `q`. -/
@[simp] theorem insertClaspComponentEquiv_symm_inl_first (s : Fin 4) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        (.inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))))) =
      .inl (D.crossingComponentOfHalfEdge (![p, q, p, q] s)) := by
  simp [insertClaspComponentEquiv, claspCollapseComponentEquiv,
    claspCollapseComponent_halfEdge, claspCollapse]

/-- Slots `0` and `2` of the second new crossing lie on the component of the arc at `q`, slots
`1` and `3` on that of the arc at `p`. -/
@[simp] theorem insertClaspComponentEquiv_symm_inl_second (s : Fin 4) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        (.inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inr s)))) =
      .inl (D.crossingComponentOfHalfEdge (![q, p, q, p] s)) := by
  simp [insertClaspComponentEquiv, claspCollapseComponentEquiv,
    claspCollapseComponent_halfEdge, claspCollapse]

/-- Inserting a clasp preserves each labelled crossing-free component. -/
@[simp] theorem insertClaspComponentEquiv_inr (i : Fin D.crossinglessComponentCount) :
    D.insertClaspComponentEquiv p q b hqp hqe (.inr i) = .inr (finCongr (by simp) i) := (rfl)

/-- Removing a clasp preserves each labelled crossing-free component. -/
@[simp] theorem insertClaspComponentEquiv_symm_inr
    (i : Fin (D.insertClasp p q b hqp hqe).crossinglessComponentCount) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm (.inr i) = .inr (finCongr (by simp) i) :=
  (rfl)

end InsertClasp

/-! ### A clasp between an arc and a crossing-free circle -/

section InsertCircleClasp

variable (D : OrientedPDCode n) (p : Fin (4 * n)) (o b : Bool)

/-- The crossing-free label of the circle that the clasp pushes across the arc. -/
private def claspedCircleLabel : Fin (D.adjoinCircle o).crossinglessComponentCount :=
  Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)

/-- The component of `D.adjoinCircle o` containing a half-edge of the circle clasp. At both new
crossings the slots alternate between the cut arc and the clasped circle. -/
private def circleClaspCollapse (x : Fin (4 * (n + 2))) : (D.adjoinCircle o).Component :=
  Sum.elim
    (fun y ↦ Sum.elim (fun z ↦ .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge z))
      (fun s ↦ ![.inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (claspedCircleLabel D o), .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (claspedCircleLabel D o)] s) ((halfEdgeSuccEquiv n).symm y))
    (fun s ↦ ![.inr (claspedCircleLabel D o),
      .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p), .inr (claspedCircleLabel D o),
      .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p)] s)
    ((halfEdgeSuccEquiv (n + 1)).symm x)

/-- Adjoining a circle keeps the component of each half-edge through a crossing turn. -/
private theorem adjoinCircle_crossingComponentOfHalfEdge_crossingTurn (z : Fin (4 * n)) :
    (D.adjoinCircle o).crossingComponentOfHalfEdge (D.crossingTurn z) =
      (D.adjoinCircle o).crossingComponentOfHalfEdge z := by
  simpa using (D.adjoinCircle o).crossingComponentOfHalfEdge_crossingTurn z

/-- Adjoining a circle keeps the component of each half-edge across its arc. -/
private theorem adjoinCircle_crossingComponentOfHalfEdge_edgePair (z : Fin (4 * n)) :
    (D.adjoinCircle o).crossingComponentOfHalfEdge (D.edgePair.val z) =
      (D.adjoinCircle o).crossingComponentOfHalfEdge z := by
  simpa using (D.adjoinCircle o).crossingComponentOfHalfEdge_edgePair z

private theorem circleClaspCollapse_crossingTurn (x : Fin (4 * (n + 2))) :
    circleClaspCollapse D p o ((D.insertCircleClasp p o b).crossingTurn x) =
      circleClaspCollapse D p o x := by
  obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
  · obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    · simp [circleClaspCollapse, adjoinCircle_crossingComponentOfHalfEdge_crossingTurn]
    · fin_cases s <;> simp [circleClaspCollapse, oppositeCrossingSlot_apply]
  · fin_cases s <;> simp [circleClaspCollapse, oppositeCrossingSlot_apply]

private theorem circleClaspCollapse_edgePair (x : Fin (4 * (n + 2))) :
    circleClaspCollapse D p o ((D.insertCircleClasp p o b).edgePair.val x) =
      circleClaspCollapse D p o x := by
  obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
  · obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    · by_cases hxp : x = p
      · subst x
        simp [circleClaspCollapse]
      by_cases hxe : x = D.edgePair.val p
      · subst x
        simp [circleClaspCollapse, adjoinCircle_crossingComponentOfHalfEdge_edgePair]
      simp [circleClaspCollapse, insertCircleClasp_edgePair_old _ p b hxp hxe,
        adjoinCircle_crossingComponentOfHalfEdge_edgePair]
    · fin_cases s <;> simp [circleClaspCollapse]
  · fin_cases s <;> simp [circleClaspCollapse, adjoinCircle_crossingComponentOfHalfEdge_edgePair]

private def circleClaspCollapseComponent :
    (D.insertCircleClasp p o b).Component → (D.adjoinCircle o).Component :=
  Sum.elim
    (CrossingComponent.lift (circleClaspCollapse D p o)
      (circleClaspCollapse_crossingTurn D p o b) (circleClaspCollapse_edgePair D p o b))
    (fun i ↦ .inr (Fin.cast (by simp)
      (Fin.cast (m := D.crossinglessComponentCount) (by simp) i).castSucc))

private theorem circleClaspCollapseComponent_halfEdge (x : Fin (4 * (n + 2))) :
    circleClaspCollapseComponent D p o b
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge x)) =
      circleClaspCollapse D p o x := by
  simp only [circleClaspCollapseComponent, Sum.elim_inl,
    CrossingComponent.lift_crossingComponentOfHalfEdge]

private theorem circleClaspCollapseComponent_inr (i : Fin D.crossinglessComponentCount) :
    circleClaspCollapseComponent D p o b (.inr (Fin.cast (by simp) i)) =
      .inr (Fin.cast (by simp) i.castSucc) := by
  simp [circleClaspCollapseComponent]

private theorem circleClaspCollapseComponent_surjective :
    Function.Surjective (circleClaspCollapseComponent D p o b) := by
  intro c
  rcases (D.adjoinCircle o).component_cases c with ⟨x, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
      (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x.val))))), ?_⟩
    rw [circleClaspCollapseComponent_halfEdge]
    simp [circleClaspCollapse]
  · obtain ⟨i, rfl⟩ := (finCongr (by simp :
        D.crossinglessComponentCount + 1 =
          (D.adjoinCircle o).crossinglessComponentCount)).surjective i
    induction i using Fin.lastCases with
    | last =>
      refine ⟨.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))), ?_⟩
      rw [circleClaspCollapseComponent_halfEdge]
      simp [circleClaspCollapse, claspedCircleLabel]
    | cast i => exact ⟨_, circleClaspCollapseComponent_inr D p o b i⟩

/-- Transport labelled components across the second Reidemeister move between an arc and a
crossing-free circle. The circle with the last crossing-free label becomes the
crossing-bearing component through the circle slots of the clasp; all old components keep
their representatives or labels. -/
def insertCircleClaspComponentEquiv :
    (D.adjoinCircle o).Component ≃ (D.insertCircleClasp p o b).Component :=
  (Equiv.ofBijective (circleClaspCollapseComponent D p o b)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨circleClaspCollapseComponent_surjective D p o b, by simp; omega⟩)).symm

private theorem insertCircleClaspComponentEquiv_symm_apply
    (c : (D.insertCircleClasp p o b).Component) :
    (D.insertCircleClaspComponentEquiv p o b).symm c = circleClaspCollapseComponent D p o b c := by
  simp only [insertCircleClaspComponentEquiv, Equiv.symm_symm, Equiv.ofBijective_apply]

/-- Under removal of the circle clasp, every old half-edge recovers its original component. -/
@[simp] theorem insertCircleClaspComponentEquiv_symm_inl_halfEdge (x : Fin (4 * n)) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))))) =
      .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge x) := by
  rw [insertCircleClaspComponentEquiv_symm_apply, circleClaspCollapseComponent_halfEdge]
  simp [circleClaspCollapse]

/-- Inserting the circle clasp preserves the component represented by each old half-edge,
including incoming half-edges. -/
@[simp] theorem insertCircleClaspComponentEquiv_inl_halfEdge (x : Fin (4 * n)) :
    D.insertCircleClaspComponentEquiv p o b
        (.inl ((D.adjoinCircle o).crossingComponentOfHalfEdge x)) =
      .inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))))) := by
  rw [← Equiv.eq_symm_apply, insertCircleClaspComponentEquiv_symm_inl_halfEdge]

/-- An old outgoing representative is transported to its included half-edge. -/
@[simp] theorem insertCircleClaspComponentEquiv_componentOfOutgoing
    (x : {x : Fin (4 * n) // (D.adjoinCircle o).orientation x = true}) :
    D.insertCircleClaspComponentEquiv p o b ((D.adjoinCircle o).componentOfOutgoing x) =
      (D.insertCircleClasp p o b).componentOfOutgoing
        ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x.val))),
          by simpa using x.property⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertCircleClaspComponentEquiv_inl_halfEdge p o b x.val

/-- At the first new crossing, slots `0` and `2` lie on the cut arc and slots `1` and `3` on
the clasped circle, which has the last crossing-free label before the move. -/
@[simp] theorem insertCircleClaspComponentEquiv_symm_inl_first (s : Fin 4) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))))) =
      ![.inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))] s := by
  rw [insertCircleClaspComponentEquiv_symm_apply, circleClaspCollapseComponent_halfEdge]
  simp [circleClaspCollapse, claspedCircleLabel]

/-- At the second new crossing, slots `0` and `2` lie on the clasped circle and slots `1` and
`3` on the cut arc. -/
@[simp] theorem insertCircleClaspComponentEquiv_symm_inl_second (s : Fin 4) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inr s)))) =
      ![.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p)] s := by
  rw [insertCircleClaspComponentEquiv_symm_apply, circleClaspCollapseComponent_halfEdge]
  simp [circleClaspCollapse, claspedCircleLabel]

/-- The clasped circle becomes the component through slot `1` of the first new crossing. -/
@[simp] theorem insertCircleClaspComponentEquiv_last :
    D.insertCircleClaspComponentEquiv p o b
        (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))) =
      .inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))) := by
  rw [← Equiv.eq_symm_apply, insertCircleClaspComponentEquiv_symm_inl_first]
  rfl

/-- Removing the circle clasp preserves every crossing-free label. -/
@[simp] theorem insertCircleClaspComponentEquiv_symm_inr (i : Fin D.crossinglessComponentCount) :
    (D.insertCircleClaspComponentEquiv p o b).symm (.inr (Fin.cast (by simp) i)) =
      .inr (Fin.cast (by simp) i.castSucc) := by
  rw [insertCircleClaspComponentEquiv_symm_apply]
  exact circleClaspCollapseComponent_inr D p o b i

/-- Inserting the circle clasp preserves every other crossing-free label, even when
orientations repeat. -/
@[simp] theorem insertCircleClaspComponentEquiv_inr_castSucc
    (i : Fin D.crossinglessComponentCount) :
    D.insertCircleClaspComponentEquiv p o b (.inr (Fin.cast (by simp) i.castSucc)) =
      .inr (Fin.cast (by simp) i) := by
  rw [← Equiv.eq_symm_apply, insertCircleClaspComponentEquiv_symm_inr]

end InsertCircleClasp

/-! ### A clasp between two crossing-free circles -/

section AdjoinTwoCircleClasp

variable (D : OrientedPDCode n) (o₁ o₂ b : Bool)

/-- The label of the first adjoined crossing-free circle, oriented by `o₁`. -/
private def firstClaspCircleLabel :
    Fin ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount :=
  Fin.cast (by simp) (Fin.last D.crossinglessComponentCount).castSucc

/-- The label of the second adjoined crossing-free circle, oriented by `o₂`. -/
private def secondClaspCircleLabel :
    Fin ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount :=
  Fin.cast (by simp) (Fin.last (D.crossinglessComponentCount + 1))

/-- The circle of the clasp through a crossing slot: at the first crossing slots `0` and `2`
lie on the first circle, at the second crossing slots `1` and `3` do. -/
private def twoCircleClaspLabel (y : Fin (4 * 2)) :
    Fin ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount :=
  ![![firstClaspCircleLabel D o₁ o₂, secondClaspCircleLabel D o₁ o₂,
      firstClaspCircleLabel D o₁ o₂, secondClaspCircleLabel D o₁ o₂],
    ![secondClaspCircleLabel D o₁ o₂, firstClaspCircleLabel D o₁ o₂,
      secondClaspCircleLabel D o₁ o₂, firstClaspCircleLabel D o₁ o₂]]
    ((crossingSlotEquiv 2).symm y).1 ((crossingSlotEquiv 2).symm y).2

private theorem twoCircleClaspLabel_crossingTurn (y : Fin (4 * 2)) :
    twoCircleClaspLabel D o₁ o₂ ((PDCode.twoCircleClasp b).crossingTurn y) =
      twoCircleClaspLabel D o₁ o₂ y := by
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective y
  have h := (PDCode.twoCircleClasp b).crossingTurn_crossing i s
  simp only [twoCircleClasp_halfEdge, Perm.one_apply, crossing_apply] at h
  rw [h]
  fin_cases i <;> fin_cases s <;> simp [twoCircleClaspLabel, oppositeCrossingSlot_apply]

private theorem twoCircleClaspLabel_edgePair (y : Fin (4 * 2)) :
    twoCircleClaspLabel D o₁ o₂ ((PDCode.twoCircleClasp b).edgePair.val y) =
      twoCircleClaspLabel D o₁ o₂ y := by
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective y
  fin_cases i <;> fin_cases s <;> simp [twoCircleClaspLabel, Equiv.permCongr_apply]

/-- The component of `(D.adjoinCircle o₁).adjoinCircle o₂` containing a half-edge of the
adjoined clasp. -/
private def twoCircleClaspCollapse (x : Fin (4 * (n + 2))) :
    ((D.adjoinCircle o₁).adjoinCircle o₂).Component :=
  Sum.elim (fun z ↦ .inl (((D.adjoinCircle o₁).adjoinCircle o₂).crossingComponentOfHalfEdge z))
    (fun y ↦ .inr (twoCircleClaspLabel D o₁ o₂ y)) ((disjointUnionHalfEdgeEquiv n 2).symm x)

private theorem twoCircleClaspCollapse_crossingTurn (x : Fin (4 * (n + 2))) :
    twoCircleClaspCollapse D o₁ o₂ ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingTurn x) =
      twoCircleClaspCollapse D o₁ o₂ x := by
  obtain ⟨z | y, rfl⟩ := (disjointUnionHalfEdgeEquiv n 2).surjective x
  · simpa [twoCircleClaspCollapse, PDCode.adjoinTwoCircleClasp_def, Equiv.permCongr_apply] using
      ((D.adjoinCircle o₁).adjoinCircle o₂).crossingComponentOfHalfEdge_crossingTurn z
  · simpa [twoCircleClaspCollapse, PDCode.adjoinTwoCircleClasp_def, Equiv.permCongr_apply] using
      twoCircleClaspLabel_crossingTurn D o₁ o₂ b y

private theorem twoCircleClaspCollapse_edgePair (x : Fin (4 * (n + 2))) :
    twoCircleClaspCollapse D o₁ o₂ ((D.adjoinTwoCircleClasp o₁ o₂ b).edgePair.val x) =
      twoCircleClaspCollapse D o₁ o₂ x := by
  obtain ⟨z | y, rfl⟩ := (disjointUnionHalfEdgeEquiv n 2).surjective x
  · simpa [twoCircleClaspCollapse, PDCode.adjoinTwoCircleClasp_def, Equiv.permCongr_apply] using
      ((D.adjoinCircle o₁).adjoinCircle o₂).crossingComponentOfHalfEdge_edgePair z
  · simpa [twoCircleClaspCollapse, PDCode.adjoinTwoCircleClasp_def, Equiv.permCongr_apply] using
      twoCircleClaspLabel_edgePair D o₁ o₂ b y

private def twoCircleClaspCollapseComponent :
    (D.adjoinTwoCircleClasp o₁ o₂ b).Component →
      ((D.adjoinCircle o₁).adjoinCircle o₂).Component :=
  Sum.elim
    (CrossingComponent.lift (twoCircleClaspCollapse D o₁ o₂)
      (twoCircleClaspCollapse_crossingTurn D o₁ o₂ b) (twoCircleClaspCollapse_edgePair D o₁ o₂ b))
    (fun i ↦ .inr (Fin.cast (by simp)
      (Fin.cast (m := D.crossinglessComponentCount) (by simp) i).castSucc.castSucc))

private theorem twoCircleClaspCollapseComponent_halfEdge (x : Fin (4 * (n + 2))) :
    twoCircleClaspCollapseComponent D o₁ o₂ b
        (.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge x)) =
      twoCircleClaspCollapse D o₁ o₂ x := by
  simp only [twoCircleClaspCollapseComponent, Sum.elim_inl,
    CrossingComponent.lift_crossingComponentOfHalfEdge]

private theorem twoCircleClaspCollapseComponent_inr (i : Fin D.crossinglessComponentCount) :
    twoCircleClaspCollapseComponent D o₁ o₂ b (.inr (Fin.cast (by simp) i)) =
      .inr (Fin.cast (by simp) i.castSucc.castSucc) := by
  simp [twoCircleClaspCollapseComponent]

private theorem twoCircleClaspCollapseComponent_surjective :
    Function.Surjective (twoCircleClaspCollapseComponent D o₁ o₂ b) := by
  intro c
  rcases ((D.adjoinCircle o₁).adjoinCircle o₂).component_cases c with ⟨x, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
      (disjointUnionHalfEdgeEquiv n 2 (.inl x.val))), ?_⟩
    rw [twoCircleClaspCollapseComponent_halfEdge]
    simp [twoCircleClaspCollapse]
  · obtain ⟨i, rfl⟩ := (finCongr (by simp :
        D.crossinglessComponentCount + 1 + 1 =
          ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount)).surjective i
    induction i using Fin.lastCases with
    | last =>
      refine ⟨.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
        (disjointUnionHalfEdgeEquiv n 2 (.inr (crossingSlotEquiv 2 (0, 1))))), ?_⟩
      rw [twoCircleClaspCollapseComponent_halfEdge]
      simp [twoCircleClaspCollapse, twoCircleClaspLabel, secondClaspCircleLabel]
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        refine ⟨.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
          (disjointUnionHalfEdgeEquiv n 2 (.inr (crossingSlotEquiv 2 (0, 0))))), ?_⟩
        rw [twoCircleClaspCollapseComponent_halfEdge]
        simp [twoCircleClaspCollapse, twoCircleClaspLabel, firstClaspCircleLabel]
      | cast i => exact ⟨_, twoCircleClaspCollapseComponent_inr D o₁ o₂ b i⟩

/-- Transport labelled components across the second Reidemeister move between two
crossing-free circles. The circles with the last two crossing-free labels, adjoined with
orientations `o₁` and then `o₂`, become the two components of the clasp; all old components
keep their representatives or labels. -/
def adjoinTwoCircleClaspComponentEquiv :
    ((D.adjoinCircle o₁).adjoinCircle o₂).Component ≃
      (D.adjoinTwoCircleClasp o₁ o₂ b).Component :=
  (Equiv.ofBijective (twoCircleClaspCollapseComponent D o₁ o₂ b)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨twoCircleClaspCollapseComponent_surjective D o₁ o₂ b, by
        rw [card_component, card_component]; simp⟩)).symm

private theorem adjoinTwoCircleClaspComponentEquiv_symm_apply
    (c : (D.adjoinTwoCircleClasp o₁ o₂ b).Component) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm c =
      twoCircleClaspCollapseComponent D o₁ o₂ b c := by
  simp only [adjoinTwoCircleClaspComponentEquiv, Equiv.symm_symm, Equiv.ofBijective_apply]

/-- Under removal of the two-circle clasp, every old half-edge recovers its original
component. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_symm_inl_halfEdge (x : Fin (4 * n)) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm
        (.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
          (disjointUnionHalfEdgeEquiv n 2 (.inl x)))) =
      .inl (((D.adjoinCircle o₁).adjoinCircle o₂).crossingComponentOfHalfEdge x) := by
  rw [adjoinTwoCircleClaspComponentEquiv_symm_apply, twoCircleClaspCollapseComponent_halfEdge]
  simp [twoCircleClaspCollapse]

/-- Adjoining the two-circle clasp preserves the component represented by each old half-edge,
including incoming half-edges. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_inl_halfEdge (x : Fin (4 * n)) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inl (((D.adjoinCircle o₁).adjoinCircle o₂).crossingComponentOfHalfEdge x)) =
      .inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
        (disjointUnionHalfEdgeEquiv n 2 (.inl x))) := by
  rw [← Equiv.eq_symm_apply, adjoinTwoCircleClaspComponentEquiv_symm_inl_halfEdge]

/-- An old outgoing representative is transported to its included half-edge. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_componentOfOutgoing
    (x : {x : Fin (4 * n) // ((D.adjoinCircle o₁).adjoinCircle o₂).orientation x = true}) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (((D.adjoinCircle o₁).adjoinCircle o₂).componentOfOutgoing x) =
      (D.adjoinTwoCircleClasp o₁ o₂ b).componentOfOutgoing
        ⟨disjointUnionHalfEdgeEquiv n 2 (.inl x.val), by
          rw [adjoinTwoCircleClasp_def, orientation_disjointUnion_inl]
          simpa using x.property⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.adjoinTwoCircleClaspComponentEquiv_inl_halfEdge o₁ o₂ b x.val

/-- Each slot of the adjoined clasp lies on one of the two clasped circles: slots `0` and `2`
of its first crossing and slots `1` and `3` of its second lie on the circle oriented by `o₁`,
the other slots on the circle oriented by `o₂`. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_symm_inl_clasp (i : Fin 2) (s : Fin 4) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm
        (.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
          (crossingSlotEquiv (n + 2) (Fin.natAdd n i, s)))) =
      .inr (![![Fin.cast (by simp) (Fin.last D.crossinglessComponentCount).castSucc,
          Fin.cast (by simp) (Fin.last (D.crossinglessComponentCount + 1)),
          Fin.cast (by simp) (Fin.last D.crossinglessComponentCount).castSucc,
          Fin.cast (by simp) (Fin.last (D.crossinglessComponentCount + 1))],
        ![Fin.cast (by simp) (Fin.last (D.crossinglessComponentCount + 1)),
          Fin.cast (by simp) (Fin.last D.crossinglessComponentCount).castSucc,
          Fin.cast (by simp) (Fin.last (D.crossinglessComponentCount + 1)),
          Fin.cast (by simp) (Fin.last D.crossinglessComponentCount).castSucc]] i s) := by
  rw [← disjointUnionHalfEdgeEquiv_inr_crossingSlot, adjoinTwoCircleClaspComponentEquiv_symm_apply,
    twoCircleClaspCollapseComponent_halfEdge]
  simp [twoCircleClaspCollapse, twoCircleClaspLabel, firstClaspCircleLabel,
    secondClaspCircleLabel]

/-- The circle oriented by `o₁` becomes the clasp component through slot `0` of its first
crossing. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_inr_first :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount).castSucc)) =
      .inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
        (crossingSlotEquiv (n + 2) (Fin.natAdd n 0, 0))) := by
  rw [← Equiv.eq_symm_apply, adjoinTwoCircleClaspComponentEquiv_symm_inl_clasp]
  rfl

/-- The circle oriented by `o₂` becomes the clasp component through slot `1` of its first
crossing. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_inr_second :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inr (Fin.cast (by simp) (Fin.last (D.crossinglessComponentCount + 1)))) =
      .inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
        (crossingSlotEquiv (n + 2) (Fin.natAdd n 0, 1))) := by
  rw [← Equiv.eq_symm_apply, adjoinTwoCircleClaspComponentEquiv_symm_inl_clasp]
  rfl

/-- Removing the two-circle clasp preserves every crossing-free label. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_symm_inr
    (i : Fin D.crossinglessComponentCount) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm (.inr (Fin.cast (by simp) i)) =
      .inr (Fin.cast (by simp) i.castSucc.castSucc) := by
  rw [adjoinTwoCircleClaspComponentEquiv_symm_apply]
  exact twoCircleClaspCollapseComponent_inr D o₁ o₂ b i

/-- Adjoining the two-circle clasp preserves every other crossing-free label, even when
orientations repeat. -/
@[simp] theorem adjoinTwoCircleClaspComponentEquiv_inr_castSucc_castSucc
    (i : Fin D.crossinglessComponentCount) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inr (Fin.cast (by simp) i.castSucc.castSucc)) =
      .inr (Fin.cast (by simp) i) := by
  rw [← Equiv.eq_symm_apply, adjoinTwoCircleClaspComponentEquiv_symm_inr]

end AdjoinTwoCircleClasp

end TauCeti.OrientedPDCode
