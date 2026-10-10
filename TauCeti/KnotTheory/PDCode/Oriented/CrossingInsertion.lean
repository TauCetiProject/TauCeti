/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.CrossingInsertion
public import TauCeti.KnotTheory.PDCode.Oriented.Reconnect

/-!
# Crossing insertion on oriented diagrams

Crossing insertion preserves the directions of the two cut arcs. Their orientation parity
determines which over-strand gives a positive crossing and which reconnection is the
oriented smoothing. These operations give an explicit skein triple of oriented codes.
They are combinatorial operations; no planarity assumption is imposed.

The construction lifts `PDCode.insertCrossing` using its arc-end computation rules.
Reference: W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 3,
Proposition 3.7.
-/

public section

namespace TauCeti.OrientedPDCode

open PDCode

variable {n : ℕ}

/-- Insert a crossing between two distinct arcs, retaining their directions.
The Boolean selects the over-strand as in `PDCode.insertCrossing`. -/
def insertCrossing (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool)
    (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p) : OrientedPDCode (n + 1) where
  toPDCode := D.toPDCode.insertCrossing p q b
  orientation x := match (halfEdgeSuccEquiv n).symm x with
    | .inl y => D.orientation y
    | .inr slot => ![!D.orientation p, !D.orientation q, D.orientation p, D.orientation q] slot
  orientation_edgePair := by
    intro x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    rcases x with x | slot
    · by_cases hxp : x = p
      · subst x
        simp [PDCode.insertCrossing_edgePair_inl_self (D := D.toPDCode) b hqp hqe]
      by_cases hxq : x = q
      · subst x
        simp [PDCode.insertCrossing_edgePair_inl_right (D := D.toPDCode) b hqp hqe]
      by_cases hxe : x = D.edgePair.val p
      · subst x
        simp [PDCode.insertCrossing_edgePair_inl_edgePair_self (D := D.toPDCode) b hqp hqe]
      by_cases hxe' : x = D.edgePair.val q
      · subst x
        simp [PDCode.insertCrossing_edgePair_inl_edgePair_right (D := D.toPDCode) b hqp hqe]
      rw [PDCode.insertCrossing_edgePair_inl_of_ne (D := D.toPDCode) b hxp hxq hxe hxe']
      simp
    · fin_cases slot <;> simp [PDCode.insertCrossing_edgePair_inr_zero (D := D.toPDCode) b hqp hqe,
        PDCode.insertCrossing_edgePair_inr_one (D := D.toPDCode) b hqp hqe,
        PDCode.insertCrossing_edgePair_inr_two (D := D.toPDCode) b hqp hqe,
        PDCode.insertCrossing_edgePair_inr_three (D := D.toPDCode) b hqp hqe]
  orientation_oppositeCrossingSlot := by
    intro i slot
    induction i using Fin.lastCases with
    | last => fin_cases slot <;> simp [oppositeCrossingSlot_apply]
    | cast i => simp
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

variable (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool)
  (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)

/-- Forgetting orientation gives the unoriented crossing insertion. -/
@[simp] theorem insertCrossing_toPDCode :
    (D.insertCrossing p q b hqp hqe).toPDCode = D.toPDCode.insertCrossing p q b := (rfl)

/-- Each old half-edge retains its direction. -/
@[simp] theorem insertCrossing_orientation_inl (x : Fin (4 * n)) :
    (D.insertCrossing p q b hqp hqe).orientation (halfEdgeSuccEquiv n (.inl x)) =
      D.orientation x := by simp [insertCrossing]

/-- The four new directions are fixed by those of the two cut arcs. -/
@[simp] theorem insertCrossing_orientation_inr (slot : Fin 4) :
    (D.insertCrossing p q b hqp hqe).orientation (halfEdgeSuccEquiv n (.inr slot)) =
      ![!D.orientation p, !D.orientation q, D.orientation p, D.orientation q] slot := by
  simp [insertCrossing]

/-- The insertion retains all oriented crossing-free components. -/
@[simp] theorem insertCrossing_crossinglessComponents :
    (D.insertCrossing p q b hqp hqe).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Each old crossing retains its sign. -/
@[simp] theorem crossingSign_insertCrossing_castSucc (i : Fin n) :
    (D.insertCrossing p q b hqp hqe).crossingSign i.castSucc = D.crossingSign i := by
  simp [crossingSign_def, crossing_apply]

/-- The new crossing is positive exactly when its over-pair agrees with the orientation parity. -/
@[simp] theorem crossingSign_insertCrossing_last :
    (D.insertCrossing p q b hqp hqe).crossingSign (Fin.last n) =
      if (D.orientation p ^^ D.orientation q) = b then 1 else -1 := by
  simp [crossingSign_def, crossing_apply]

/-- Insertion changes the writhe by exactly the new crossing sign. -/
@[simp] theorem writhe_insertCrossing :
    (D.insertCrossing p q b hqp hqe).writhe =
      D.writhe + if (D.orientation p ^^ D.orientation q) = b then 1 else -1 := by
  simp [writhe_def, Fin.sum_univ_castSucc]

/-- Smooth the inserted crossing in the orientation-preserving way.
Oppositely directed ends are joined directly; equally directed ends are joined to the
other end of the second arc. -/
def orientedSmoothing (D : OrientedPDCode n) (p q : Fin (4 * n)) : OrientedPDCode n :=
  D.reconnect p (bif D.orientation p ^^ D.orientation q then q else D.edgePair.val q) (by
    generalize hp : D.orientation p = a
    generalize hq : D.orientation q = c
    cases a <;> cases c <;> simp_all)

/-- The unoriented smoothing is the reconnection selected by orientation parity. -/
@[simp] theorem orientedSmoothing_toPDCode :
    (D.orientedSmoothing p q).toPDCode =
      D.toPDCode.reconnect p
        (bif D.orientation p ^^ D.orientation q then q else D.edgePair.val q) := by
  simp [orientedSmoothing]

/-- Oriented smoothing retains all half-edge directions. -/
@[simp] theorem orientedSmoothing_orientation (x : Fin (4 * n)) :
    (D.orientedSmoothing p q).orientation x = D.orientation x := by simp [orientedSmoothing]

/-- Oriented smoothing retains the oriented crossing-free components. -/
@[simp] theorem orientedSmoothing_crossinglessComponents :
    (D.orientedSmoothing p q).crossinglessComponents = D.crossinglessComponents := by
  simp [orientedSmoothing]

/-- The smoothing has the same writhe as the diagram before insertion. -/
@[simp] theorem writhe_orientedSmoothing : (D.orientedSmoothing p q).writhe = D.writhe := by
  simp [orientedSmoothing]

end TauCeti.OrientedPDCode
