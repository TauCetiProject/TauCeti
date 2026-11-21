/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ClaspInsertion.Planar
public import TauCeti.KnotTheory.PDCode.Oriented.Component

/-!
# Clasp insertion on oriented PD-codes

`TauCeti.PDCode.insertClasp` cuts two arcs of a PD-code open and routes them through a clasp of
two new crossings; when the two arcs border a common face this is the second Reidemeister move.
This file lifts the insertion to oriented codes. Each cut arc keeps its direction, which fixes the
orientations of the eight new half-edges, so the oriented insertion takes no data beyond the
unoriented one.

Whatever the directions of the two arcs, the two new crossings have opposite signs: they have the
same orientation parity, and the same strand is over at both, which with the slot conventions of a
clasp means opposite over-pair indicators. The insertion therefore keeps the writhe. Together with
the invariance of the Kauffman bracket (`TauCeti.PDCode.kauffmanBracket_insertClasp`), this makes
the writhe-normalized Kauffman bracket invariant under the oriented insertion, and in particular
under the oriented second Reidemeister move.

`TauCeti.OrientedPDCode.insertClaspComponentEquiv` tracks individual link components across the
insertion: every old half-edge stays on its original component, the slots along each cut arc belong
to that arc's component, and each crossing-free circle label is fixed.

## Main definitions

* `TauCeti.OrientedPDCode.insertClasp`: insert a clasp into two arcs of an oriented code.
* `TauCeti.OrientedPDCode.insertClaspComponentEquiv`: the labelled component bijection across an
  oriented clasp insertion.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_insertClasp_last`: the two new crossings have opposite
  signs.
* `TauCeti.OrientedPDCode.writhe_insertClasp`: the insertion keeps the writhe.
* `TauCeti.OrientedPDCode.normalizedKauffmanBracket_insertClasp`: the writhe-normalized Kauffman
  bracket is invariant under the insertion.
* `TauCeti.OrientedPDCode.mirror_insertClasp` and `TauCeti.OrientedPDCode.reverse_insertClasp`:
  the insertion commutes with reflection and with reversal.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the writhe and the Jones polynomial from the bracket).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3 (oriented component traversal).
-/

public section

namespace TauCeti

namespace OrientedPDCode

open Equiv Equiv.Perm PDCode

variable {n : ℕ}

/-- **Clasp insertion on an oriented PD-code**: the clasp insertion
`TauCeti.PDCode.insertClasp` into the arc ending at `p` and the distinct arc ending at `q`, with
each cut arc keeping its direction. Along the arc ending at `p`, the new half-edges at slots `0`
and `2` of the first new crossing and at slots `1` and `3` of the second alternate between the
orientations `!D.orientation p` and `D.orientation p`, and likewise along the arc ending at `q`
through slots `1` and `3` of the first new crossing and slots `0` and `2` of the second. -/
def insertClasp (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
    (hqe : q ≠ D.edgePair.val p) : OrientedPDCode (n + 2) where
  toPDCode := D.toPDCode.insertClasp p q b hqp hqe
  orientation x :=
    match (halfEdgeSuccEquiv (n + 1)).symm x with
    | .inl y =>
      match (halfEdgeSuccEquiv n).symm y with
      | .inl z => D.orientation z
      | .inr slot => ![!D.orientation p, !D.orientation q, D.orientation p, D.orientation q] slot
    | .inr slot => ![!D.orientation q, !D.orientation p, D.orientation q, D.orientation p] slot
  orientation_edgePair := by
    intro x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot
      · by_cases hxp : x = p
        · subst x
          simp
        by_cases hxe : x = D.edgePair.val p
        · subst x
          simp
        by_cases hxq : x = q
        · subst x
          simp
        by_cases hxe' : x = D.edgePair.val q
        · subst x
          simp
        simp [D.toPDCode.insertClasp_edgePair_inl_inl_of_ne p q b hqp hqe hxp hxe hxq hxe']
      · fin_cases slot <;> simp
    · fin_cases slot <;> simp
  orientation_oppositeCrossingSlot := by
    intro i slot
    induction i using Fin.lastCases with
    | last => fin_cases slot <;> simp [oppositeCrossingSlot_apply]
    | cast i =>
      induction i using Fin.lastCases with
      | last => fin_cases slot <;> simp [oppositeCrossingSlot_apply]
      | cast i => simp
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

variable (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
  (hqe : q ≠ D.edgePair.val p)

/-- Forgetting the orientation of the oriented clasp insertion gives the unoriented one. -/
@[simp]
theorem toPDCode_insertClasp :
    (D.insertClasp p q b hqp hqe).toPDCode = D.toPDCode.insertClasp p q b hqp hqe :=
  (rfl)

/-- The oriented clasp insertion keeps the orientation of every old half-edge. -/
@[simp]
theorem orientation_insertClasp_inl_inl (x : Fin (4 * n)) :
    (D.insertClasp p q b hqp hqe).orientation
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) =
      D.orientation x := by
  simp [insertClasp]

/-- The orientations of the slots of the first new crossing: slots `0` and `2` lie on the arc
ending at `p`, slots `1` and `3` on the arc ending at `q`. -/
@[simp]
theorem orientation_insertClasp_inl_inr (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).orientation
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr slot)))) =
      ![!D.orientation p, !D.orientation q, D.orientation p, D.orientation q] slot := by
  simp [insertClasp]

/-- The orientations of the slots of the second new crossing: slots `0` and `2` lie on the arc
ending at `q`, slots `1` and `3` on the arc ending at `p`. -/
@[simp]
theorem orientation_insertClasp_inr (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).orientation (halfEdgeSuccEquiv (n + 1) (.inr slot)) =
      ![!D.orientation q, !D.orientation p, D.orientation q, D.orientation p] slot := by
  simp [insertClasp]

/-- The oriented clasp insertion keeps the oriented crossing-free components. -/
@[simp]
theorem crossinglessComponents_insertClasp :
    (D.insertClasp p q b hqp hqe).crossinglessComponents = D.crossinglessComponents :=
  (rfl)

/-- Every old crossing keeps its sign after the oriented clasp insertion. -/
@[simp]
theorem crossingSign_insertClasp_castSucc_castSucc (i : Fin n) :
    (D.insertClasp p q b hqp hqe).crossingSign i.castSucc.castSucc = D.crossingSign i := by
  simp [crossingSign_def, crossing_apply]

/-- The first new crossing is positive exactly when the parity of the directions of the two cut
arcs is its over-pair indicator `b`. -/
@[simp]
theorem crossingSign_insertClasp_castSucc_last :
    (D.insertClasp p q b hqp hqe).crossingSign (Fin.last n).castSucc =
      if (D.orientation p ^^ D.orientation q) = b then 1 else -1 := by
  simp [crossingSign_def, crossing_apply]

/-- **The two new crossings of an oriented clasp have opposite signs.** -/
@[simp]
theorem crossingSign_insertClasp_last :
    (D.insertClasp p q b hqp hqe).crossingSign (Fin.last (n + 1)) =
      -(D.insertClasp p q b hqp hqe).crossingSign (Fin.last n).castSucc := by
  rw [crossingSign_insertClasp_castSucc_last, crossingSign_def]
  simp only [crossing_apply, toPDCode_insertClasp, crossingSlotEquiv_succ_last,
    insertClasp_crossing_last, orientation_insertClasp_inr, insertClasp_overPair_last]
  generalize D.orientation p = x
  generalize D.orientation q = y
  cases x <;> cases y <;> cases b <;> simp

/-- **The oriented clasp insertion keeps the writhe.** -/
@[simp]
theorem writhe_insertClasp : (D.insertClasp p q b hqp hqe).writhe = D.writhe := by
  rw [writhe_def, writhe_def, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    crossingSign_insertClasp_last]
  simp

/-- **The writhe-normalized Kauffman bracket is invariant under the oriented clasp insertion**,
in particular under the oriented second Reidemeister move. -/
@[simp]
theorem normalizedKauffmanBracket_insertClasp {R : Type*} [CommRing R] (a : Rˣ) :
    (D.insertClasp p q b hqp hqe).normalizedKauffmanBracket a =
      D.normalizedKauffmanBracket a := by
  rw [normalizedKauffmanBracket_def, normalizedKauffmanBracket_def, writhe_insertClasp,
    toPDCode_insertClasp, kauffmanBracket_insertClasp]

/-- Reflecting the oriented clasp insertion inserts the clasp with the other strand over into the
reflected code. -/
@[simp]
theorem mirror_insertClasp :
    (D.insertClasp p q b hqp hqe).mirror =
      D.mirror.insertClasp p q (!b) hqp (by rwa [mirror_toPDCode, mirror_edgePair]) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot <;> simp
    · simp
  · simp

/-- Reversing the oriented clasp insertion inserts the clasp into the reversed code. -/
@[simp]
theorem reverse_insertClasp :
    (D.insertClasp p q b hqp hqe).reverse =
      D.reverse.insertClasp p q b hqp (by rwa [reverse_toPDCode]) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot
      · simp
      · fin_cases slot <;> simp
    · fin_cases slot <;> simp
  · simp

/-! ### Component transport -/

noncomputable section

private def collapseClaspHalfEdge (x : Fin (4 * (n + 2))) : D.CrossingComponent :=
  match (halfEdgeSuccEquiv (n + 1)).symm x with
  | .inl y =>
    match (halfEdgeSuccEquiv n).symm y with
    | .inl z => D.crossingComponentOfHalfEdge z
    | .inr s =>
      ![D.crossingComponentOfHalfEdge p, D.crossingComponentOfHalfEdge q,
        D.crossingComponentOfHalfEdge p, D.crossingComponentOfHalfEdge q] s
  | .inr s =>
    ![D.crossingComponentOfHalfEdge q, D.crossingComponentOfHalfEdge p,
      D.crossingComponentOfHalfEdge q, D.crossingComponentOfHalfEdge p] s

private theorem collapseClaspHalfEdge_crossingTurn (x : Fin (4 * (n + 2))) :
    collapseClaspHalfEdge D p q ((D.insertClasp p q b hqp hqe).crossingTurn x) =
      collapseClaspHalfEdge D p q x := by
  obtain ⟨y, rfl⟩ := (D.insertClasp p q b hqp hqe).halfEdge.surjective x
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv (n + 2)).surjective y
  rw [PDCode.crossingTurn_crossing, ← PDCode.crossing_apply]
  induction i using Fin.lastCases with
  | last =>
    simp only [PDCode.crossing_apply, toPDCode_insertClasp, crossingSlotEquiv_succ_last,
      PDCode.insertClasp_crossing_last]
    fin_cases s <;> simp [collapseClaspHalfEdge, oppositeCrossingSlot_apply]
  | cast i =>
    induction i using Fin.lastCases with
    | last =>
      simp only [PDCode.crossing_apply, toPDCode_insertClasp, crossingSlotEquiv_succ_castSucc,
        crossingSlotEquiv_succ_last, PDCode.insertClasp_crossing_castSucc_last]
      fin_cases s <;> simp [collapseClaspHalfEdge, oppositeCrossingSlot_apply]
    | cast i =>
      simp only [PDCode.crossing_apply, toPDCode_insertClasp, crossingSlotEquiv_succ_castSucc,
        PDCode.insertClasp_crossing_castSucc_castSucc]
      simpa only [collapseClaspHalfEdge, Equiv.symm_apply_apply, ← PDCode.crossingTurn_crossing,
        ← PDCode.crossing_apply] using D.crossingComponentOfHalfEdge_crossingTurn (D.crossing i s)

private theorem collapseClaspHalfEdge_edgePair (x : Fin (4 * (n + 2))) :
    collapseClaspHalfEdge D p q ((D.insertClasp p q b hqp hqe).edgePair.val x) =
      collapseClaspHalfEdge D p q x := by
  obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
  rcases x with x | s
  · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    rcases x with x | s
    · by_cases hxp : x = p
      · subst x; simp [collapseClaspHalfEdge]
      by_cases hxe : x = D.edgePair.val p
      · subst x; simp [collapseClaspHalfEdge]
      by_cases hxq : x = q
      · subst x; simp [collapseClaspHalfEdge]
      by_cases hxe' : x = D.edgePair.val q
      · subst x; simp [collapseClaspHalfEdge]
      simp [collapseClaspHalfEdge,
        D.toPDCode.insertClasp_edgePair_inl_inl_of_ne p q b hqp hqe hxp hxe hxq hxe']
    · fin_cases s <;> simp [collapseClaspHalfEdge]
  · fin_cases s <;> simp [collapseClaspHalfEdge]

private def collapseClaspCrossingComponent :
    (D.insertClasp p q b hqp hqe).CrossingComponent → D.CrossingComponent :=
  (D.insertClasp p q b hqp hqe).liftCrossingComponent (collapseClaspHalfEdge D p q)
    (collapseClaspHalfEdge_crossingTurn D p q b hqp hqe)
    (collapseClaspHalfEdge_edgePair D p q b hqp hqe)

private theorem collapseClaspCrossingComponent_surjective :
    Function.Surjective (collapseClaspCrossingComponent D p q b hqp hqe) := by
  intro c
  obtain ⟨⟨x, hx⟩, rfl⟩ := Quotient.mk_surjective c
  refine ⟨(D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
    (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))), ?_⟩
  rw [collapseClaspCrossingComponent, liftCrossingComponent_crossingComponentOfHalfEdge]
  simpa [collapseClaspHalfEdge] using D.crossingComponentOfHalfEdge_of_outgoing x hx

private def collapseClaspCrossingComponentEquiv :
    (D.insertClasp p q b hqp hqe).CrossingComponent ≃ D.CrossingComponent :=
  Equiv.ofBijective (collapseClaspCrossingComponent D p q b hqp hqe)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨collapseClaspCrossingComponent_surjective D p q b hqp hqe, by simp⟩)

/-- Inserting an oriented clasp into two distinct arcs transports every old component by half-edge
inclusion and keeps each crossing-free circle label fixed. Its inverse collapses the slots along
each cut arc back to that arc's component. -/
def insertClaspComponentEquiv :
    D.Component ≃ (D.insertClasp p q b hqp hqe).Component :=
  Equiv.sumCongr
    (collapseClaspCrossingComponentEquiv D p q b hqp hqe).symm (finCongr (by simp))

/-- Under clasp removal, every old half-edge recovers its original component. -/
@[simp]
theorem insertClaspComponentEquiv_symm_inl_old (x : Fin (4 * n)) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        (.inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))))) =
      .inl (D.crossingComponentOfHalfEdge x) := by
  simp [insertClaspComponentEquiv, collapseClaspCrossingComponentEquiv,
    collapseClaspCrossingComponent, collapseClaspHalfEdge]

/-- Inserting a clasp preserves the component represented by each old half-edge, incoming or
outgoing. -/
@[simp]
theorem insertClaspComponentEquiv_inl_halfEdge (x : Fin (4 * n)) :
    D.insertClaspComponentEquiv p q b hqp hqe (.inl (D.crossingComponentOfHalfEdge x)) =
      .inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))))) := by
  apply (D.insertClaspComponentEquiv p q b hqp hqe).symm.injective
  simp

/-- An old outgoing representative is transported to its included half-edge. -/
@[simp]
theorem insertClaspComponentEquiv_componentOfOutgoing
    (x : {x : Fin (4 * n) // D.orientation x = true}) :
    D.insertClaspComponentEquiv p q b hqp hqe (D.componentOfOutgoing x) =
      (D.insertClasp p q b hqp hqe).componentOfOutgoing
        ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x.val))),
          by simpa using x.property⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertClaspComponentEquiv_inl_halfEdge p q b hqp hqe x.val

/-- Removing a clasp sends every old outgoing representative back to itself. -/
@[simp]
theorem insertClaspComponentEquiv_symm_componentOfOutgoing_old (x : Fin (4 * n))
    (hx : (D.insertClasp p q b hqp hqe).orientation
      (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) = true) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        ((D.insertClasp p q b hqp hqe).componentOfOutgoing
          ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x))), hx⟩) =
      D.componentOfOutgoing ⟨x, by simpa using hx⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertClaspComponentEquiv_symm_inl_old p q b hqp hqe x

/-- At the first new crossing, slots `0` and `2` belong to the component of `p` and slots `1` and
`3` belong to the component of `q`. -/
@[simp]
theorem insertClaspComponentEquiv_symm_inl_first (s : Fin 4) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        (.inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))))) =
      .inl (![D.crossingComponentOfHalfEdge p, D.crossingComponentOfHalfEdge q,
        D.crossingComponentOfHalfEdge p, D.crossingComponentOfHalfEdge q] s) := by
  simp [insertClaspComponentEquiv, collapseClaspCrossingComponentEquiv,
    collapseClaspCrossingComponent, collapseClaspHalfEdge]

/-- At the first new crossing, an outgoing slot collapses to the component of `p` at slots `0` and
`2`, and to the component of `q` at slots `1` and `3`. -/
@[simp]
theorem insertClaspComponentEquiv_symm_componentOfOutgoing_first (s : Fin 4)
    (hs : (D.insertClasp p q b hqp hqe).orientation
      (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))) = true) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        ((D.insertClasp p q b hqp hqe).componentOfOutgoing
          ⟨halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s))), hs⟩) =
      .inl (![D.crossingComponentOfHalfEdge p, D.crossingComponentOfHalfEdge q,
        D.crossingComponentOfHalfEdge p, D.crossingComponentOfHalfEdge q] s) := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertClaspComponentEquiv_symm_inl_first p q b hqp hqe s

/-- At the second new crossing, slots `0` and `2` belong to the component of `q` and slots `1` and
`3` belong to the component of `p`. -/
@[simp]
theorem insertClaspComponentEquiv_symm_inl_second (s : Fin 4) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        (.inl ((D.insertClasp p q b hqp hqe).crossingComponentOfHalfEdge
          (halfEdgeSuccEquiv (n + 1) (.inr s)))) =
      .inl (![D.crossingComponentOfHalfEdge q, D.crossingComponentOfHalfEdge p,
        D.crossingComponentOfHalfEdge q, D.crossingComponentOfHalfEdge p] s) := by
  simp [insertClaspComponentEquiv, collapseClaspCrossingComponentEquiv,
    collapseClaspCrossingComponent, collapseClaspHalfEdge]

/-- At the second new crossing, an outgoing slot collapses to the component of `q` at slots `0` and
`2`, and to the component of `p` at slots `1` and `3`. -/
@[simp]
theorem insertClaspComponentEquiv_symm_componentOfOutgoing_second (s : Fin 4)
    (hs : (D.insertClasp p q b hqp hqe).orientation (halfEdgeSuccEquiv (n + 1) (.inr s)) = true) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm
        ((D.insertClasp p q b hqp hqe).componentOfOutgoing
          ⟨halfEdgeSuccEquiv (n + 1) (.inr s), hs⟩) =
      .inl (![D.crossingComponentOfHalfEdge q, D.crossingComponentOfHalfEdge p,
        D.crossingComponentOfHalfEdge q, D.crossingComponentOfHalfEdge p] s) := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.insertClaspComponentEquiv_symm_inl_second p q b hqp hqe s

/-- Inserting a clasp preserves each labelled crossing-free component. -/
@[simp]
theorem insertClaspComponentEquiv_inr (i : Fin D.crossinglessComponentCount) :
    D.insertClaspComponentEquiv p q b hqp hqe (.inr i) = .inr (Fin.cast (by simp) i) := by
  simp [insertClaspComponentEquiv]

/-- Removing a clasp preserves each labelled crossing-free component. -/
@[simp]
theorem insertClaspComponentEquiv_symm_inr
    (i : Fin (D.insertClasp p q b hqp hqe).crossinglessComponentCount) :
    (D.insertClaspComponentEquiv p q b hqp hqe).symm (.inr i) =
      .inr (Fin.cast (by simp) i) := by
  simp [insertClaspComponentEquiv]

end

end OrientedPDCode

end TauCeti
