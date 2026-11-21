/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Circles

/-!
# Component transport for circle-involving second Reidemeister moves

When a second Reidemeister move pushes a crossing-free circle across an arc, or clasps two
crossing-free circles together, crossing-free labels become crossing-bearing traversal classes.
This file constructs the explicit component bijections for both moves:

* `OrientedPDCode.insertCircleClaspComponentEquiv` identifies the components of `D.adjoinCircle o`
  with those of `D.insertCircleClasp p o b`. It carries each old half-edge to its inclusion, sends
  the newly adjoined circle label `Fin.last` to the component of the clasp's circle strand, and
  preserves every older crossing-free circle label.
* `OrientedPDCode.twoCircleClaspComponentEquiv` identifies `Fin 2` with the two components of the
  closed two-circle clasp `OrientedPDCode.twoCircleClasp o₁ o₂ b`, sending `0` to the strand of
  direction `o₁` and `1` to the strand of direction `o₂`.
* `OrientedPDCode.adjoinTwoCircleClaspComponentEquiv` identifies the components of
  `(D.adjoinCircle o₁).adjoinCircle o₂` with those of `D.adjoinTwoCircleClasp o₁ o₂ b` by
  combining `twoCircleClaspComponentEquiv` with `OrientedPDCode.disjointUnionComponentEquiv`. The
  two last crossing-free labels `(Fin.last _).castSucc` and `Fin.last _` map respectively to the
  `o₁` and `o₂` strands of the adjoined clasp, while all components of `D` retain their half-edge
  representatives or crossing-free labels.

No planarity or nonemptiness hypothesis on the surrounding diagram is required.

## Main definitions

* `TauCeti.OrientedPDCode.insertCircleClaspComponentEquiv`: component bijection for the second
  Reidemeister move between an arc and a crossing-free circle.
* `TauCeti.OrientedPDCode.twoCircleClaspComponentEquiv`: component bijection between `Fin 2` and the
  closed two-circle clasp.
* `TauCeti.OrientedPDCode.adjoinTwoCircleClaspComponentEquiv`: component bijection for the second
  Reidemeister move between two crossing-free circles.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (the Reidemeister moves).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3 (oriented component traversal).
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open Equiv Equiv.Perm PDCode

/-! ### Circle-and-arc second Reidemeister move -/

section CircleArc

variable {n : ℕ} (D : OrientedPDCode n) (p : Fin (4 * n)) (o b : Bool)

private def collapseCircleClaspHalfEdge (x : Fin (4 * (n + 2))) : (D.adjoinCircle o).Component :=
  let arcComp : (D.adjoinCircle o).Component :=
    .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p)
  let circleComp : (D.adjoinCircle o).Component :=
    .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))
  match (halfEdgeSuccEquiv (n + 1)).symm x with
  | .inl y =>
    match (halfEdgeSuccEquiv n).symm y with
    | .inl z => .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge z)
    | .inr s => ![arcComp, circleComp, arcComp, circleComp] s
  | .inr s => ![circleComp, arcComp, circleComp, arcComp] s

private theorem collapseCircleClaspHalfEdge_crossingTurn (x : Fin (4 * (n + 2))) :
    collapseCircleClaspHalfEdge D p o ((D.insertCircleClasp p o b).crossingTurn x) =
      collapseCircleClaspHalfEdge D p o x := by
  obtain ⟨y, rfl⟩ := (D.insertCircleClasp p o b).halfEdge.surjective x
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv (n + 2)).surjective y
  rw [PDCode.crossingTurn_crossing, ← PDCode.crossing_apply]
  induction i using Fin.lastCases with
  | last =>
    simp only [PDCode.crossing_apply, toPDCode_insertCircleClasp, crossingSlotEquiv_succ_last,
      PDCode.insertCircleClasp_crossing_last]
    fin_cases s <;> simp [collapseCircleClaspHalfEdge, oppositeCrossingSlot_apply]
  | cast i =>
    induction i using Fin.lastCases with
    | last =>
      simp only [PDCode.crossing_apply, toPDCode_insertCircleClasp,
        crossingSlotEquiv_succ_castSucc, crossingSlotEquiv_succ_last,
        PDCode.insertCircleClasp_crossing_castSucc_last]
      fin_cases s <;> simp [collapseCircleClaspHalfEdge, oppositeCrossingSlot_apply]
    | cast i =>
      simp only [PDCode.crossing_apply, toPDCode_insertCircleClasp,
        crossingSlotEquiv_succ_castSucc, PDCode.insertCircleClasp_crossing_castSucc_castSucc,
        collapseCircleClaspHalfEdge, Equiv.symm_apply_apply]
      rw [Sum.inl.injEq]
      have hturn :
          D.halfEdge (crossingSlotEquiv n (i, oppositeCrossingSlot s)) =
            (D.adjoinCircle o).crossingTurn (D.halfEdge (crossingSlotEquiv n (i, s))) := by
        simp [PDCode.crossing_apply]
      rw [hturn, crossingComponentOfHalfEdge_crossingTurn]

private theorem collapseCircleClaspHalfEdge_edgePair (x : Fin (4 * (n + 2))) :
    collapseCircleClaspHalfEdge D p o ((D.insertCircleClasp p o b).edgePair.val x) =
      collapseCircleClaspHalfEdge D p o x := by
  obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
  rcases x with x | s
  · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    rcases x with x | s
    · by_cases hx : x = p
      · subst x; simp [collapseCircleClaspHalfEdge]
      by_cases hx' : x = D.edgePair.val p
      · subst x
        simp only [collapseCircleClaspHalfEdge, toPDCode_insertCircleClasp,
          PDCode.insertCircleClasp_edgePair_old_partner, Equiv.symm_apply_apply]
        have hedge : D.edgePair.val p = (D.adjoinCircle o).edgePair.val p := by simp
        simp [hedge]
      simp only [collapseCircleClaspHalfEdge, toPDCode_insertCircleClasp,
        D.toPDCode.insertCircleClasp_edgePair_old p b hx hx', Equiv.symm_apply_apply]
      have hedge : D.edgePair.val x = (D.adjoinCircle o).edgePair.val x := by simp
      simp [hedge]
    · rw [toPDCode_insertCircleClasp, D.toPDCode.insertCircleClasp_edgePair_first]
      fin_cases s <;> simp [collapseCircleClaspHalfEdge]
  · rw [toPDCode_insertCircleClasp, D.toPDCode.insertCircleClasp_edgePair_second]
    have hedge : D.edgePair.val p = (D.adjoinCircle o).edgePair.val p := by simp
    fin_cases s <;> simp [collapseCircleClaspHalfEdge, hedge]

private def collapseCircleClaspComponent :
    (D.insertCircleClasp p o b).Component → (D.adjoinCircle o).Component :=
  Sum.elim
    ((D.insertCircleClasp p o b).liftCrossingComponent (collapseCircleClaspHalfEdge D p o)
      (collapseCircleClaspHalfEdge_crossingTurn D p o b)
      (collapseCircleClaspHalfEdge_edgePair D p o b))
    fun i ↦ .inr (Fin.cast (by simp) i.castSucc)

private theorem collapseCircleClaspComponent_inl_halfEdge (x : Fin (4 * (n + 2))) :
    collapseCircleClaspComponent D p o b
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge x)) =
      collapseCircleClaspHalfEdge D p o x :=
  (D.insertCircleClasp p o b).liftCrossingComponent_crossingComponentOfHalfEdge _ _ _ x

private theorem collapseCircleClaspComponent_inr (i : Fin D.crossinglessComponentCount) :
    collapseCircleClaspComponent D p o b (.inr (Fin.cast (by simp) i)) =
      .inr (Fin.cast (by simp) i.castSucc) := by
  simp [collapseCircleClaspComponent, Fin.ext_iff]

private theorem collapseCircleClaspComponent_surjective :
    Function.Surjective (collapseCircleClaspComponent D p o b) := by
  intro c
  rcases (D.adjoinCircle o).component_cases c with ⟨x, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
      (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x.val))))), ?_⟩
    rw [collapseCircleClaspComponent_inl_halfEdge]
    simp [collapseCircleClaspHalfEdge]
  · obtain ⟨i, rfl⟩ := (finCongr (by simp :
        D.crossinglessComponentCount + 1 =
          (D.adjoinCircle o).crossinglessComponentCount)).surjective i
    induction i using Fin.lastCases with
    | last =>
      refine ⟨.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr 1))))), ?_⟩
      rw [collapseCircleClaspComponent_inl_halfEdge]
      simp [collapseCircleClaspHalfEdge, finCongr]
    | cast i =>
      exact ⟨.inr (Fin.cast (by simp) i), collapseCircleClaspComponent_inr D p o b i⟩

/-- Transport labelled components across the circle-and-arc second Reidemeister move. The newly
adjoined circle with label `Fin.last` becomes the circle strand of the clasp, while all old
components retain their half-edge representatives or crossing-free labels. -/
def insertCircleClaspComponentEquiv :
    (D.adjoinCircle o).Component ≃ (D.insertCircleClasp p o b).Component :=
  (Equiv.ofBijective (collapseCircleClaspComponent D p o b)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨collapseCircleClaspComponent_surjective D p o b, by
        simp only [card_component, toPDCode_insertCircleClasp, toPDCode_adjoinCircle,
          componentCount_insertCircleClasp]⟩)).symm

private theorem insertCircleClaspComponentEquiv_symm_apply
    (c : (D.insertCircleClasp p o b).Component) :
    (D.insertCircleClaspComponentEquiv p o b).symm c =
      collapseCircleClaspComponent D p o b c := by
  simp only [insertCircleClaspComponentEquiv, Equiv.symm_symm, Equiv.ofBijective_apply]

/-- Removing the circle-and-arc clasp recovers the component of every old half-edge. -/
@[simp]
theorem insertCircleClaspComponentEquiv_symm_inl_old (x : Fin (4 * n)) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))))) =
      .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge x) := by
  rw [insertCircleClaspComponentEquiv_symm_apply, collapseCircleClaspComponent_inl_halfEdge]
  simp [collapseCircleClaspHalfEdge]

/-- Inserting the circle-and-arc clasp carries each old half-edge's component by inclusion. -/
@[simp]
theorem insertCircleClaspComponentEquiv_inl_halfEdge (x : Fin (4 * n)) :
    D.insertCircleClaspComponentEquiv p o b
        (.inl ((D.adjoinCircle o).crossingComponentOfHalfEdge x)) =
      .inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))))) := by
  apply (D.insertCircleClaspComponentEquiv p o b).symm.injective
  simp

/-- Old outgoing representatives are carried by the native half-edge inclusion. -/
@[simp]
theorem insertCircleClaspComponentEquiv_componentOfOutgoing
    (x : {x : Fin (4 * n) // (D.adjoinCircle o).orientation x = true}) :
    D.insertCircleClaspComponentEquiv p o b ((D.adjoinCircle o).componentOfOutgoing x) =
      (D.insertCircleClasp p o b).componentOfOutgoing
        ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x.val))),
          by simpa using x.property⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertCircleClaspComponentEquiv_inl_halfEdge p o b x.val

/-- Removing the circle-and-arc clasp sends every old outgoing representative back to itself. -/
@[simp]
theorem insertCircleClaspComponentEquiv_symm_componentOfOutgoing_old (x : Fin (4 * n))
    (hx : (D.insertCircleClasp p o b).orientation
      (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) = true) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        ((D.insertCircleClasp p o b).componentOfOutgoing
          ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))), hx⟩) =
      (D.adjoinCircle o).componentOfOutgoing ⟨x, by simpa using hx⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertCircleClaspComponentEquiv_symm_inl_old p o b x

/-- At the first new crossing, slots `0` and `2` collapse to the cut arc's component and slots `1`
and `3` collapse to the consumed crossing-free label `Fin.last`. -/
@[simp]
theorem insertCircleClaspComponentEquiv_symm_inl_first (s : Fin 4) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))))) =
      ![.inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))] s := by
  rw [insertCircleClaspComponentEquiv_symm_apply, collapseCircleClaspComponent_inl_halfEdge]
  simp [collapseCircleClaspHalfEdge]

/-- At the first new crossing, an outgoing slot collapses to the cut arc's component at slots `0`
and `2`, and to the consumed crossing-free label `Fin.last` at slots `1` and `3`. -/
@[simp]
theorem insertCircleClaspComponentEquiv_symm_componentOfOutgoing_first (s : Fin 4)
    (hs : (D.insertCircleClasp p o b).orientation
      (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))) = true) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        ((D.insertCircleClasp p o b).componentOfOutgoing
          ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s))), hs⟩) =
      ![.inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))] s := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertCircleClaspComponentEquiv_symm_inl_first p o b s

/-- At the second new crossing, slots `0` and `2` collapse to the consumed crossing-free label
`Fin.last` and slots `1` and `3` collapse to the cut arc's component. -/
@[simp]
theorem insertCircleClaspComponentEquiv_symm_inl_second (s : Fin 4) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        (.inl ((D.insertCircleClasp p o b).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inr s)))) =
      ![.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p)] s := by
  rw [insertCircleClaspComponentEquiv_symm_apply, collapseCircleClaspComponent_inl_halfEdge]
  simp [collapseCircleClaspHalfEdge]

/-- At the second new crossing, an outgoing slot collapses to the consumed crossing-free label
`Fin.last` at slots `0` and `2`, and to the cut arc's component at slots `1` and `3`. -/
@[simp]
theorem insertCircleClaspComponentEquiv_symm_componentOfOutgoing_second (s : Fin 4)
    (hs : (D.insertCircleClasp p o b).orientation (halfEdgeSuccEquiv (n + 1) (.inr s)) = true) :
    (D.insertCircleClaspComponentEquiv p o b).symm
        ((D.insertCircleClasp p o b).componentOfOutgoing
          ⟨halfEdgeSuccEquiv (n + 1) (.inr s), hs⟩) =
      ![.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p),
        .inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount)),
        .inl ((D.adjoinCircle o).crossingComponentOfHalfEdge p)] s := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertCircleClaspComponentEquiv_symm_inl_second p o b s

/-- The added-circle label `Fin.last` maps to the circle strand of the clasp, represented at the
first new crossing by slot `3` when `o = true` and slot `1` otherwise. -/
@[simp]
theorem insertCircleClaspComponentEquiv_inr_last :
    D.insertCircleClaspComponentEquiv p o b
        (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount))) =
      (D.insertCircleClasp p o b).componentOfOutgoing
        ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr (if o then 3 else 1)))),
          by cases o <;> simp⟩ := by
  apply (D.insertCircleClaspComponentEquiv p o b).symm.injective
  rw [Equiv.symm_apply_apply, ← inl_crossingComponentOfHalfEdge,
    insertCircleClaspComponentEquiv_symm_inl_first]
  cases o <;> simp

/-- Removing the circle-and-arc clasp preserves every older crossing-free circle label. -/
@[simp]
theorem insertCircleClaspComponentEquiv_symm_inr
    (i : Fin (D.insertCircleClasp p o b).crossinglessComponentCount) :
    (D.insertCircleClaspComponentEquiv p o b).symm (.inr i) =
      .inr (Fin.cast (by simp)
        (Fin.cast (by simp) i : Fin D.crossinglessComponentCount).castSucc) := by
  rw [insertCircleClaspComponentEquiv_symm_apply]
  simpa using collapseCircleClaspComponent_inr D p o b (Fin.cast (by simp) i)

/-- Every older crossing-free circle label is preserved across the circle-and-arc move. -/
@[simp]
theorem insertCircleClaspComponentEquiv_inr_castSucc (i : Fin D.crossinglessComponentCount) :
    D.insertCircleClaspComponentEquiv p o b (.inr (Fin.cast (by simp) i.castSucc)) =
      .inr (Fin.cast (by simp) i) := by
  rw [← Equiv.eq_symm_apply, insertCircleClaspComponentEquiv_symm_inr]
  simp

end CircleArc

/-! ### Closed clasp on two circles and its adjunction -/

section TwoCircles

private def collapseTwoCircleClaspHalfEdge (x : Fin 8) : Fin 2 :=
  let p := (crossingSlotEquiv 2).symm x
  (if p.1 = 0 then ![0, 1, 0, 1] else ![1, 0, 1, 0]) p.2

private theorem collapseTwoCircleClaspHalfEdge_crossingTurn (o₁ o₂ b : Bool) (x : Fin 8) :
    collapseTwoCircleClaspHalfEdge ((twoCircleClasp o₁ o₂ b).crossingTurn x) =
      collapseTwoCircleClaspHalfEdge x := by
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective x
  have hh : (twoCircleClasp o₁ o₂ b).crossingTurn (crossingSlotEquiv 2 (i, s)) =
      crossingSlotEquiv 2 (i, oppositeCrossingSlot s) := by
    simpa [PDCode.crossing_apply] using (twoCircleClasp o₁ o₂ b).toPDCode.crossingTurn_crossing i s
  rw [hh]
  fin_cases i <;> fin_cases s <;> simp [collapseTwoCircleClaspHalfEdge, oppositeCrossingSlot_apply]

private theorem collapseTwoCircleClaspHalfEdge_edgePair (o₁ o₂ b : Bool) (x : Fin 8) :
    collapseTwoCircleClaspHalfEdge ((twoCircleClasp o₁ o₂ b).edgePair.val x) =
      collapseTwoCircleClaspHalfEdge x := by
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective x
  simp only [toPDCode_twoCircleClasp, PDCode.twoCircleClasp_edgePair_val, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, Equiv.prodCongr_apply]
  fin_cases i <;> fin_cases s <;> simp [collapseTwoCircleClaspHalfEdge]

private def collapseTwoCircleClaspComponent (o₁ o₂ b : Bool) :
    (twoCircleClasp o₁ o₂ b).Component → Fin 2 :=
  Sum.elim
    ((twoCircleClasp o₁ o₂ b).liftCrossingComponent collapseTwoCircleClaspHalfEdge
      (collapseTwoCircleClaspHalfEdge_crossingTurn o₁ o₂ b)
      (collapseTwoCircleClaspHalfEdge_edgePair o₁ o₂ b))
    fun i ↦ Fin.elim0 (Fin.cast (by simp) i)

private theorem collapseTwoCircleClaspComponent_inl_halfEdge (o₁ o₂ b : Bool) (x : Fin 8) :
    collapseTwoCircleClaspComponent o₁ o₂ b
        (.inl ((twoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge x)) =
      collapseTwoCircleClaspHalfEdge x :=
  (twoCircleClasp o₁ o₂ b).liftCrossingComponent_crossingComponentOfHalfEdge _ _ _ x

private theorem collapseTwoCircleClaspComponent_surjective (o₁ o₂ b : Bool) :
    Function.Surjective (collapseTwoCircleClaspComponent o₁ o₂ b) := by
  intro k
  fin_cases k
  · refine ⟨.inl ((twoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
      (crossingSlotEquiv 2 (0, 0))), ?_⟩
    rw [collapseTwoCircleClaspComponent_inl_halfEdge]
    simp [collapseTwoCircleClaspHalfEdge]
  · refine ⟨.inl ((twoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
      (crossingSlotEquiv 2 (0, 1))), ?_⟩
    rw [collapseTwoCircleClaspComponent_inl_halfEdge]
    simp [collapseTwoCircleClaspHalfEdge]

/-- Identify `Fin 2` with the two components of the closed oriented clasp: `0` corresponds to the
circle of direction `o₁` (slots `0` and `2` at crossing `0`, slots `1` and `3` at crossing `1`),
and `1` corresponds to the circle of direction `o₂` (slots `1` and `3` at crossing `0`, slots `0`
and `2` at crossing `1`). -/
def twoCircleClaspComponentEquiv (o₁ o₂ b : Bool) :
    Fin 2 ≃ (twoCircleClasp o₁ o₂ b).Component :=
  (Equiv.ofBijective (collapseTwoCircleClaspComponent o₁ o₂ b)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨collapseTwoCircleClaspComponent_surjective o₁ o₂ b, by
        rw [card_component, toPDCode_twoCircleClasp, PDCode.componentCount_twoCircleClasp]
        simp⟩)).symm

private theorem twoCircleClaspComponentEquiv_symm_apply (o₁ o₂ b : Bool)
    (c : (twoCircleClasp o₁ o₂ b).Component) :
    (twoCircleClaspComponentEquiv o₁ o₂ b).symm c =
      collapseTwoCircleClaspComponent o₁ o₂ b c := by
  simp only [twoCircleClaspComponentEquiv, Equiv.symm_symm, Equiv.ofBijective_apply]

/-- Each crossing slot of the closed two-circle clasp collapses to `0` on the `o₁` strand and `1`
on the `o₂` strand. -/
@[simp]
theorem twoCircleClaspComponentEquiv_symm_inl_halfEdge (o₁ o₂ b : Bool) (i : Fin 2) (s : Fin 4) :
    (twoCircleClaspComponentEquiv o₁ o₂ b).symm
        (.inl ((twoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
          (crossingSlotEquiv 2 (i, s)))) =
      (if i = 0 then ![0, 1, 0, 1] else ![1, 0, 1, 0]) s := by
  rw [twoCircleClaspComponentEquiv_symm_apply, collapseTwoCircleClaspComponent_inl_halfEdge]
  simp [collapseTwoCircleClaspHalfEdge]

/-- Each outgoing crossing slot of the closed two-circle clasp collapses to `0` on the `o₁` strand
and `1` on the `o₂` strand. -/
@[simp]
theorem twoCircleClaspComponentEquiv_symm_componentOfOutgoing (o₁ o₂ b : Bool)
    (i : Fin 2) (s : Fin 4)
    (hs : (twoCircleClasp o₁ o₂ b).orientation (crossingSlotEquiv 2 (i, s)) = true) :
    (twoCircleClaspComponentEquiv o₁ o₂ b).symm
        ((twoCircleClasp o₁ o₂ b).componentOfOutgoing ⟨crossingSlotEquiv 2 (i, s), hs⟩) =
      (if i = 0 then ![0, 1, 0, 1] else ![1, 0, 1, 0]) s := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    twoCircleClaspComponentEquiv_symm_inl_halfEdge o₁ o₂ b i s

/-- Label `0` maps to the `o₁` strand of `twoCircleClasp`, represented at crossing `0` by slot `2`
when `o₁ = true` and slot `0` otherwise. -/
@[simp]
theorem twoCircleClaspComponentEquiv_zero (o₁ o₂ b : Bool) :
    twoCircleClaspComponentEquiv o₁ o₂ b 0 =
      (twoCircleClasp o₁ o₂ b).componentOfOutgoing
        ⟨crossingSlotEquiv 2 (0, if o₁ then 2 else 0), by
          rw [orientation_twoCircleClasp]; cases o₁ <;> simp⟩ := by
  apply (twoCircleClaspComponentEquiv o₁ o₂ b).symm.injective
  rw [Equiv.symm_apply_apply, ← inl_crossingComponentOfHalfEdge,
    twoCircleClaspComponentEquiv_symm_inl_halfEdge]
  cases o₁ <;> simp

/-- Label `1` maps to the `o₂` strand of `twoCircleClasp`, represented at crossing `0` by slot `3`
when `o₂ = true` and slot `1` otherwise. -/
@[simp]
theorem twoCircleClaspComponentEquiv_one (o₁ o₂ b : Bool) :
    twoCircleClaspComponentEquiv o₁ o₂ b 1 =
      (twoCircleClasp o₁ o₂ b).componentOfOutgoing
        ⟨crossingSlotEquiv 2 (0, if o₂ then 3 else 1), by
          rw [orientation_twoCircleClasp]; cases o₂ <;> simp⟩ := by
  apply (twoCircleClaspComponentEquiv o₁ o₂ b).symm.injective
  rw [Equiv.symm_apply_apply, ← inl_crossingComponentOfHalfEdge,
    twoCircleClaspComponentEquiv_symm_inl_halfEdge]
  cases o₂ <;> simp

private def componentCongr {m : ℕ} {E F : OrientedPDCode m} (h : E = F) :
    E.Component ≃ F.Component :=
  Equiv.cast (congrArg Component h)

private theorem componentCongr_inl_halfEdge {m : ℕ} {E F : OrientedPDCode m} (h : E = F)
    (x : Fin (4 * m)) :
    componentCongr h (.inl (E.crossingComponentOfHalfEdge x)) =
      .inl (F.crossingComponentOfHalfEdge x) := by
  subst h; rfl

private theorem componentCongr_symm_inl_halfEdge {m : ℕ} {E F : OrientedPDCode m} (h : E = F)
    (x : Fin (4 * m)) :
    (componentCongr h).symm (.inl (F.crossingComponentOfHalfEdge x)) =
      .inl (E.crossingComponentOfHalfEdge x) := by
  subst h; rfl

private theorem componentCongr_inr {m : ℕ} {E F : OrientedPDCode m} (h : E = F)
    (i : Fin E.crossinglessComponentCount) :
    componentCongr h (.inr i) = .inr (Fin.cast (by rw [h]) i) := by
  subst h; rfl

/-- Transport labelled components across the two-circle second Reidemeister move. All components of
`D` retain their half-edge representatives or crossing-free labels, while the two adjoined circle
labels `(Fin.last D.crossinglessComponentCount).castSucc` and
`Fin.last (D.crossinglessComponentCount + 1)` become the `o₁` and `o₂` strands of the adjoined
clasp. -/
def adjoinTwoCircleClaspComponentEquiv {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    ((D.adjoinCircle o₁).adjoinCircle o₂).Component ≃
      (D.adjoinTwoCircleClasp o₁ o₂ b).Component :=
  ((Equiv.sumCongr
      (((D.adjoinCircle o₁).adjoinCircleCrossingComponentEquiv o₂).symm.trans
        (D.adjoinCircleCrossingComponentEquiv o₁).symm)
      ((finCongr (by simp [Nat.add_assoc])).trans finSumFinEquiv.symm)).trans
    (Equiv.sumAssoc _ _ _).symm).trans
    ((Equiv.sumCongr (Equiv.refl D.Component)
      (twoCircleClaspComponentEquiv o₁ o₂ b)).trans
      ((D.disjointUnionComponentEquiv (twoCircleClasp o₁ o₂ b)).symm.trans
        (componentCongr (adjoinTwoCircleClasp_def D o₁ o₂ b).symm)))

/-- Every old half-edge of `D` keeps its component across the two-circle clasp move. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_inl_halfEdge {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) (x : Fin (4 * n)) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inl (((D.adjoinCircle o₁).adjoinCircle o₂).crossingComponentOfHalfEdge x)) =
      .inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
        (disjointUnionHalfEdgeEquiv n 2 (.inl x))) := by
  simp [adjoinTwoCircleClaspComponentEquiv, componentCongr_inl_halfEdge]

/-- Removing the adjoined two-circle clasp recovers the component of every old half-edge. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_symm_inl_old {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) (x : Fin (4 * n)) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm
        (.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
          (disjointUnionHalfEdgeEquiv n 2 (.inl x)))) =
      .inl (((D.adjoinCircle o₁).adjoinCircle o₂).crossingComponentOfHalfEdge x) := by
  apply (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).injective
  simp

/-- Old outgoing representatives are carried by left disjoint-union half-edge inclusion. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_componentOfOutgoing {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool)
    (x : {x : Fin (4 * n) // ((D.adjoinCircle o₁).adjoinCircle o₂).orientation x = true}) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (((D.adjoinCircle o₁).adjoinCircle o₂).componentOfOutgoing x) =
      (D.adjoinTwoCircleClasp o₁ o₂ b).componentOfOutgoing
        ⟨disjointUnionHalfEdgeEquiv n 2 (.inl x.val), by
          rw [adjoinTwoCircleClasp_def, orientation_disjointUnion_inl]
          simpa using x.property⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.adjoinTwoCircleClaspComponentEquiv_inl_halfEdge o₁ o₂ b x.val

/-- Removing the adjoined two-circle clasp sends every old outgoing representative back to
itself. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_symm_componentOfOutgoing_old {n : ℕ}
    (D : OrientedPDCode n) (o₁ o₂ b : Bool) (x : Fin (4 * n))
    (hx : (D.adjoinTwoCircleClasp o₁ o₂ b).orientation
      (disjointUnionHalfEdgeEquiv n 2 (.inl x)) = true) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm
        ((D.adjoinTwoCircleClasp o₁ o₂ b).componentOfOutgoing
          ⟨disjointUnionHalfEdgeEquiv n 2 (.inl x), hx⟩) =
      ((D.adjoinCircle o₁).adjoinCircle o₂).componentOfOutgoing
        ⟨x, by
          rw [adjoinTwoCircleClasp_def, orientation_disjointUnion_inl] at hx
          simpa using hx⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.adjoinTwoCircleClaspComponentEquiv_symm_inl_old o₁ o₂ b x

/-- Every original crossing-free circle label of `D` is preserved across the two-circle move. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_inr_castSucc_castSucc {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) (i : Fin D.crossinglessComponentCount) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inr (Fin.cast (by simp) i.castSucc.castSucc)) =
      .inr (Fin.cast (by simp) i) := by
  have hcast : finCongr (by simp [Nat.add_assoc] :
      ((D.adjoinCircle o₁).adjoinCircle o₂).crossinglessComponentCount =
        D.crossinglessComponentCount + 2)
      (Fin.cast (by simp) i.castSucc.castSucc) = Fin.castAdd 2 i := by
    ext
    simp
  simp [adjoinTwoCircleClaspComponentEquiv, hcast, componentCongr_inr, Equiv.sumAssoc,
    Fin.ext_iff]

/-- Removing the adjoined two-circle clasp restores every original crossing-free circle label. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_symm_inr {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) (i : Fin (D.adjoinTwoCircleClasp o₁ o₂ b).crossinglessComponentCount) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm (.inr i) =
      .inr (Fin.cast (by simp) (Fin.cast (by simp) i :
        Fin D.crossinglessComponentCount).castSucc.castSucc) := by
  apply (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).injective
  simp

/-- Removing the adjoined two-circle clasp collapses the `o₁` and `o₂` clasp strands back to the
crossing-free labels `(Fin.last D.crossinglessComponentCount).castSucc` and
`Fin.last (D.crossinglessComponentCount + 1)`. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_symm_inl_new {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) (i : Fin 2) (s : Fin 4) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm
        (.inl ((D.adjoinTwoCircleClasp o₁ o₂ b).crossingComponentOfHalfEdge
          (crossingSlotEquiv (n + 2) (Fin.natAdd n i, s)))) =
      .inr (Fin.cast (by simp)
        (![(Fin.last D.crossinglessComponentCount).castSucc,
          Fin.last (D.crossinglessComponentCount + 1)]
          ((if i = 0 then ![0, 1, 0, 1] else ![1, 0, 1, 0]) s))) := by
  rw [← disjointUnionHalfEdgeEquiv_inr_crossingSlot]
  simp only [adjoinTwoCircleClaspComponentEquiv, Equiv.symm_trans_apply,
    componentCongr_symm_inl_halfEdge, Equiv.symm_symm,
    disjointUnionComponentEquiv_inl_halfEdge_inr, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Sum.map_inr, twoCircleClaspComponentEquiv_symm_inl_halfEdge, Equiv.sumAssoc_apply_inr,
    finCongr_symm]
  congr 1
  fin_cases i <;> fin_cases s <;>
    simp [Fin.ext_iff, finSumFinEquiv_apply_right]

/-- Removing the adjoined two-circle clasp collapses each outgoing slot of the new crossings back
to the crossing-free label of its strand. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_symm_componentOfOutgoing_new {n : ℕ}
    (D : OrientedPDCode n) (o₁ o₂ b : Bool) (i : Fin 2) (s : Fin 4)
    (hs : (D.adjoinTwoCircleClasp o₁ o₂ b).orientation
      (crossingSlotEquiv (n + 2) (Fin.natAdd n i, s)) = true) :
    (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm
        ((D.adjoinTwoCircleClasp o₁ o₂ b).componentOfOutgoing
          ⟨crossingSlotEquiv (n + 2) (Fin.natAdd n i, s), hs⟩) =
      .inr (Fin.cast (by simp)
        (![(Fin.last D.crossinglessComponentCount).castSucc,
          Fin.last (D.crossinglessComponentCount + 1)]
          ((if i = 0 then ![0, 1, 0, 1] else ![1, 0, 1, 0]) s))) := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.adjoinTwoCircleClaspComponentEquiv_symm_inl_new o₁ o₂ b i s

/-- The first adjoined circle label `(Fin.last D.crossinglessComponentCount).castSucc` maps to the
`o₁` strand of the adjoined clasp. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_inr_castSucc_last {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inr (Fin.cast (by simp) (Fin.last D.crossinglessComponentCount).castSucc)) =
      (D.adjoinTwoCircleClasp o₁ o₂ b).componentOfOutgoing
        ⟨crossingSlotEquiv (n + 2) (Fin.natAdd n 0, if o₁ then 2 else 0), by
          rw [← disjointUnionHalfEdgeEquiv_inr_crossingSlot, adjoinTwoCircleClasp_def,
            orientation_disjointUnion_inr, orientation_twoCircleClasp]
          cases o₁ <;> simp⟩ := by
  apply (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm.injective
  rw [Equiv.symm_apply_apply, ← inl_crossingComponentOfHalfEdge,
    adjoinTwoCircleClaspComponentEquiv_symm_inl_new]
  cases o₁ <;> simp

/-- The second adjoined circle label `Fin.last (D.crossinglessComponentCount + 1)` maps to the `o₂`
strand of the adjoined clasp. -/
@[simp]
theorem adjoinTwoCircleClaspComponentEquiv_inr_last {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) :
    D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
        (.inr (Fin.cast (by simp) (Fin.last (D.crossinglessComponentCount + 1)))) =
      (D.adjoinTwoCircleClasp o₁ o₂ b).componentOfOutgoing
        ⟨crossingSlotEquiv (n + 2) (Fin.natAdd n 0, if o₂ then 3 else 1), by
          rw [← disjointUnionHalfEdgeEquiv_inr_crossingSlot, adjoinTwoCircleClasp_def,
            orientation_disjointUnion_inr, orientation_twoCircleClasp]
          cases o₂ <;> simp⟩ := by
  apply (D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b).symm.injective
  rw [Equiv.symm_apply_apply, ← inl_crossingComponentOfHalfEdge,
    adjoinTwoCircleClaspComponentEquiv_symm_inl_new]
  cases o₂ <;> simp

end TwoCircles

end TauCeti.OrientedPDCode
