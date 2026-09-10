/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.Basic
public import TauCeti.KnotTheory.PDCode
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic.FinCases

/-!
# From Gauss codes to PD-codes

A based oriented Gauss code records the two visits to every crossing in traversal order. An
oriented PD-code instead records the four half-edges at every crossing, their cyclic order, and
the arcs pairing them. This file gives the canonical passage from the former presentation to the
latter.

Each visit is split into an incoming and an outgoing half-edge. The outgoing half-edge at a visit
is paired with the incoming half-edge at the next visit, cyclically. At a crossing, the unique over
visit and the unique under visit determine the two opposite pairs of slots; the sign determines
which direction the under-strand takes through its pair. This convention makes the crossing sign
of the resulting PD-code literally the sign stored by the Gauss code.

The crossing-free Gauss code represents one oriented circle, rather than the empty link, so its
image is the one-component crossing-free PD-code. For a code with crossings the cyclic traversal
uses every visit and therefore contributes no crossing-free component.

The construction is a direct combinatorial-to-combinatorial edge between the diagram presentations
developed here. It follows the PD convention of M. Mastin, *Links and Planar
Diagram Codes*, Definitions 2--3, and the oriented crossing convention of W. B. R. Lickorish,
*An Introduction to Knot Theory*, Chapter 1.

## Main definitions

* `TauCeti.BasedOrientedGaussCode.visitDataEquiv` identifies a visit with its crossing label and
  over/under status.
* `TauCeti.BasedOrientedGaussCode.halfEdgeEquiv` splits visits into incoming and outgoing
  half-edges.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode` converts a based oriented Gauss code to an
  oriented PD-code.

## Main results

* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_edgePair_outgoing` says that the output follows
  the traversal order.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_isOver_crossing` identifies the PD over-strand
  with the over visit of the Gauss code.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_crossingSign` proves preservation of crossing
  signs.
-/

public section

namespace TauCeti

namespace BasedOrientedGaussCode

variable {n : ℕ}

/-!
### Visits and crossing data
-/

/-- A visit, read as its crossing label together with whether it is the over visit. -/
def visitData (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) : Fin n × Bool :=
  (D.visit i, D.over i)

/-- The two components of the data attached to a visit are its crossing label and over/under
status. -/
@[simp]
theorem visitData_apply (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.visitData i = (D.visit i, D.over i) := (rfl)

/-- The crossing label and over/under status determine a unique visit. -/
theorem visitData_bijective (D : BasedOrientedGaussCode n) : Function.Bijective D.visitData := by
  constructor
  · intro i j hij
    have hvis : D.visit i = D.visit j := congrArg Prod.fst hij
    have hover : D.over i = D.over j := congrArg Prod.snd hij
    rcases (D.visit_eq_iff i j).mp hvis with rfl | hj
    · rfl
    · rw [hj, D.over_partner] at hover
      cases h : D.over i <;> simp [h] at hover
  · rintro ⟨c, over⟩
    obtain ⟨i, hi⟩ := D.visit_surjective c
    by_cases hover : D.over i = over
    · exact ⟨i, Prod.ext hi hover⟩
    · refine ⟨D.partner.val i, Prod.ext (D.visit_partner i |>.trans hi) ?_⟩
      change D.over (D.partner.val i) = over
      rw [D.over_partner]
      cases hiOver : D.over i <;> cases over <;> simp_all

/-- Visits are equivalent to pairs consisting of a crossing and an over/under choice. -/
noncomputable def visitDataEquiv (D : BasedOrientedGaussCode n) : Fin (2 * n) ≃ Fin n × Bool :=
  Equiv.ofBijective D.visitData D.visitData_bijective

/-- The visit equivalence sends a visit to its crossing label and over/under status. -/
@[simp]
theorem visitDataEquiv_apply (D : BasedOrientedGaussCode n) (i : Fin (2 * n)) :
    D.visitDataEquiv i = (D.visit i, D.over i) := (rfl)

/-!
### The four slots of an oriented crossing
-/

/-- The slot data at a positive crossing: whether the strand is over, and whether the half-edge
points out of the crossing. Slots zero and two are the over-strand. -/
private def positiveSlotEquiv : Fin 4 ≃ Bool × Bool where
  toFun slot := if slot = 0 then (true, false) else if slot = 1 then (false, false)
    else if slot = 2 then (true, true) else (false, true)
  invFun data := if data = (true, false) then 0 else if data = (false, false) then 1
    else if data = (true, true) then 2 else 3
  left_inv slot := by fin_cases slot <;> decide
  right_inv data := by
    rcases data with ⟨over, outgoing⟩
    cases over <;> cases outgoing <;> decide

/-- The slot data at a negative crossing. It differs from the positive convention by reversing
the direction of the under-strand. -/
private def negativeSlotEquiv : Fin 4 ≃ Bool × Bool where
  toFun slot := if slot = 0 then (true, false) else if slot = 1 then (false, true)
    else if slot = 2 then (true, true) else (false, false)
  invFun data := if data = (true, false) then 0 else if data = (false, true) then 1
    else if data = (true, true) then 2 else 3
  left_inv slot := by fin_cases slot <;> decide
  right_inv data := by
    rcases data with ⟨over, outgoing⟩
    cases over <;> cases outgoing <;> decide

/-- The over/under and incoming/outgoing data assigned to the four slots of a crossing of sign
`sign`. -/
private def slotEquiv (sign : ℤˣ) : Fin 4 ≃ Bool × Bool :=
  if sign = 1 then positiveSlotEquiv else negativeSlotEquiv

private theorem slotEquiv_fst (sign : ℤˣ) (slot : Fin 4) :
    (slotEquiv sign slot).1 = decide (slot = 0 ∨ slot = 2) := by
  rcases Int.units_eq_one_or sign with rfl | rfl <;> fin_cases slot <;> decide

private theorem slotEquiv_snd_opposite (sign : ℤˣ) (slot : Fin 4) :
    (slotEquiv sign (PDCode.oppositeCrossingSlot slot)).2 = !(slotEquiv sign slot).2 := by
  have hopposite : PDCode.oppositeCrossingSlot slot = slot + 2 := by
    apply Fin.ext
    exact PDCode.oppositeCrossingSlot_apply slot
  rw [hopposite]
  rcases Int.units_eq_one_or sign with rfl | rfl
  · fin_cases slot <;> simp [slotEquiv, positiveSlotEquiv]
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    fin_cases slot <;> simp [slotEquiv, negativeSlotEquiv, hne]

/-- The visit occupying a crossing slot. Opposite slots use the same visit; slots zero and two
use the over visit, while slots one and three use the under visit. -/
noncomputable def crossingVisit (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    Fin (2 * n) :=
  D.visitDataEquiv.symm (c, decide (slot = 0 ∨ slot = 2))

/-- The incoming/outgoing direction of a crossing slot. At a positive crossing slots zero and one
are incoming; at a negative crossing slots zero and three are incoming. -/
def crossingOutgoing (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) : Bool :=
  if D.sign c = 1 then decide (slot = 2 ∨ slot = 3) else decide (slot = 1 ∨ slot = 2)

/-- The incoming/outgoing direction at a crossing, expanded in terms of the crossing sign and
slot number. -/
theorem crossingOutgoing_def (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    D.crossingOutgoing c slot =
      if D.sign c = 1 then decide (slot = 2 ∨ slot = 3) else decide (slot = 1 ∨ slot = 2) :=
  (rfl)

/-- The slot direction is the second component of the internal slot equivalence. -/
private theorem slotEquiv_snd (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    (slotEquiv (D.sign c) slot).2 = D.crossingOutgoing c slot := by
  rcases Int.units_eq_one_or (D.sign c) with h | h
  · fin_cases slot <;> simp [crossingOutgoing, slotEquiv, positiveSlotEquiv, h]
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    fin_cases slot <;> simp [crossingOutgoing, slotEquiv, negativeSlotEquiv, h, hne]

/-- Reading back the crossing visit recovers its crossing label. -/
@[simp]
theorem visit_crossingVisit (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    D.visit (D.crossingVisit c slot) = c := by
  have h := D.visitDataEquiv.apply_symm_apply (c, decide (slot = 0 ∨ slot = 2))
  rw [D.visitDataEquiv_apply] at h
  exact congrArg Prod.fst h

/-- Slots zero and two use the over visit; slots one and three use the under visit. -/
@[simp]
theorem over_crossingVisit (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    D.over (D.crossingVisit c slot) = decide (slot = 0 ∨ slot = 2) := by
  have h := D.visitDataEquiv.apply_symm_apply (c, decide (slot = 0 ∨ slot = 2))
  rw [D.visitDataEquiv_apply] at h
  exact congrArg Prod.snd h

/-- At each crossing, the four slots are equivalent to an over/under visit and an
incoming/outgoing end of that visit. -/
private def crossingSlotDataEquiv (D : BasedOrientedGaussCode n) :
    Fin n × Fin 4 ≃ (Fin n × Bool) × Bool where
  toFun p := ((p.1, (slotEquiv (D.sign p.1) p.2).1), (slotEquiv (D.sign p.1) p.2).2)
  invFun p := (p.1.1, (slotEquiv (D.sign p.1.1)).symm (p.1.2, p.2))
  left_inv p := by simp
  right_inv p := by simp

/-!
### Half-edges and traversal
-/

/-- Split each visit into its incoming (`false`) and outgoing (`true`) half-edge and enumerate the
resulting `4 * n` half-edges. -/
def halfEdgeEquiv (n : ℕ) : Fin (2 * n) × Bool ≃ Fin (4 * n) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans <|
    finProdFinEquiv.trans (finCongr (by omega))

/-- The labelled half-edge belonging to one end of a visit. -/
def halfEdge (i : Fin (2 * n)) (outgoing : Bool) : Fin (4 * n) :=
  halfEdgeEquiv n (i, outgoing)

/-- Decoding a labelled visit end recovers that visit and its incoming/outgoing choice. -/
@[simp]
theorem halfEdgeEquiv_symm_halfEdge (i : Fin (2 * n)) (outgoing : Bool) :
    (halfEdgeEquiv n).symm (halfEdge i outgoing) = (i, outgoing) := by
  simp [halfEdge]

/-- On visit ends, arc pairing joins an outgoing half-edge to the incoming half-edge of the next
visit, and conversely joins an incoming half-edge to the outgoing half-edge of the previous visit.
-/
private def traversalEdgePerm (n : ℕ) : Equiv.Perm (Fin (2 * n) × Bool) where
  toFun p := if p.2 then (finRotate _ p.1, false) else ((finRotate _).symm p.1, true)
  invFun p := if p.2 then (finRotate _ p.1, false) else ((finRotate _).symm p.1, true)
  left_inv p := by
    rcases p with ⟨i, outgoing⟩
    cases outgoing
    · exact Prod.ext (Equiv.apply_symm_apply (finRotate _) i) rfl
    · exact Prod.ext (Equiv.symm_apply_apply (finRotate _) i) rfl
  right_inv p := by
    rcases p with ⟨i, outgoing⟩
    cases outgoing
    · exact Prod.ext (Equiv.apply_symm_apply (finRotate _) i) rfl
    · exact Prod.ext (Equiv.symm_apply_apply (finRotate _) i) rfl

/-- Arc pairing on visit ends is a perfect matching. -/
private def traversalEdgePair (n : ℕ) : PerfectMatching (Fin (2 * n) × Bool) :=
  PerfectMatching.mk (traversalEdgePerm n)
    (fun p => (traversalEdgePerm n).left_inv p)
    (by rintro ⟨i, outgoing⟩ h; cases outgoing <;> simp [traversalEdgePerm] at h)

/-- The permutation that places the four crossing slots into the half-edge enumeration induced by
the Gauss traversal. -/
private noncomputable def crossingHalfEdgeEquiv (D : BasedOrientedGaussCode n) :
    Fin n × Fin 4 ≃ Fin (4 * n) :=
  (crossingSlotDataEquiv D).trans <|
    (Equiv.prodCongr D.visitDataEquiv.symm (Equiv.refl Bool)).trans (halfEdgeEquiv n)

private theorem crossingHalfEdgeEquiv_apply (D : BasedOrientedGaussCode n)
    (c : Fin n) (slot : Fin 4) :
    crossingHalfEdgeEquiv D (c, slot) =
      halfEdge (D.crossingVisit c slot) (D.crossingOutgoing c slot) := by
  simp [crossingHalfEdgeEquiv, crossingSlotDataEquiv, crossingVisit, halfEdge,
    slotEquiv_fst, slotEquiv_snd]

/-!
### Conversion to a PD-code
-/

/-- Convert a based oriented Gauss code into an oriented PD-code. The chosen base point is used
only to number the visits; forgetting the half-edge labels forgets that choice. -/
noncomputable def toOrientedPDCode (D : BasedOrientedGaussCode n) : OrientedPDCode n where
  halfEdge := (PDCode.crossingSlotEquiv n).symm.trans (crossingHalfEdgeEquiv D)
  edgePair := PerfectMatching.congr (halfEdgeEquiv n) (traversalEdgePair n)
  crossinglessComponentCount := if n = 0 then 1 else 0
  overPair := fun _ => false
  orientation := fun h => ((halfEdgeEquiv n).symm h).2
  orientation_edgePair := by
    intro h
    rw [PerfectMatching.congr_val_apply]
    obtain ⟨i, outgoing⟩ := (halfEdgeEquiv n).symm h
    rw [Equiv.symm_apply_apply]
    cases outgoing <;> simp [traversalEdgePair, traversalEdgePerm]
  orientation_oppositeCrossingSlot := by
    intro c slot
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, crossingHalfEdgeEquiv_apply,
      halfEdgeEquiv_symm_halfEdge]
    rw [← slotEquiv_snd D c (PDCode.oppositeCrossingSlot slot), ← slotEquiv_snd D c slot]
    exact slotEquiv_snd_opposite (D.sign c) slot
  crossinglessComponents := if n = 0 then {true} else 0
  crossinglessComponents_card := by split <;> simp_all

/-- The converted code uses slots zero and two for the over-strand at every crossing. -/
@[simp]
theorem toOrientedPDCode_overPair (D : BasedOrientedGaussCode n) (c : Fin n) :
    D.toOrientedPDCode.overPair c = false := (rfl)

/-- The converted Gauss code has one crossing-free component precisely in the zero-crossing
case. -/
@[simp]
theorem toOrientedPDCode_crossinglessComponentCount (D : BasedOrientedGaussCode n) :
    D.toOrientedPDCode.crossinglessComponentCount = if n = 0 then 1 else 0 := (rfl)

/-- The orientation of the crossing-free component in the zero-crossing case is the canonical
positive choice. -/
@[simp]
theorem toOrientedPDCode_crossinglessComponents (D : BasedOrientedGaussCode n) :
    D.toOrientedPDCode.crossinglessComponents = if n = 0 then {true} else 0 := (rfl)

/-- The conversion sends the crossing-free Gauss code to the positively oriented crossing-free
unknot, not to the empty link. -/
@[simp]
theorem toOrientedPDCode_empty :
    (empty : BasedOrientedGaussCode 0).toOrientedPDCode = orientedPDCodeUnlink {true} := by
  calc
    _ = orientedPDCodeUnlink
        (empty : BasedOrientedGaussCode 0).toOrientedPDCode.crossinglessComponents :=
      orientedPDCode_eq_unlink _
    _ = orientedPDCodeUnlink {true} := by
      congr 1

/-- The outgoing half-edge at a visit is paired with the incoming half-edge at the next visit. -/
@[simp]
theorem toOrientedPDCode_edgePair_outgoing (D : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) :
    D.toOrientedPDCode.edgePair.val (halfEdge i true) = halfEdge (finRotate _ i) false := by
  simp [toOrientedPDCode, halfEdge, traversalEdgePair, traversalEdgePerm]

/-- The incoming half-edge at a visit is paired with the outgoing half-edge at the previous
visit. -/
@[simp]
theorem toOrientedPDCode_edgePair_incoming (D : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) :
    D.toOrientedPDCode.edgePair.val (halfEdge i false) =
      halfEdge ((finRotate _).symm i) true := by
  simp [toOrientedPDCode, halfEdge, traversalEdgePair, traversalEdgePerm]

/-- The direction decoration remembers which half-edge of a visit is outgoing. -/
@[simp]
theorem toOrientedPDCode_orientation_halfEdge (D : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) (outgoing : Bool) :
    D.toOrientedPDCode.orientation (halfEdge i outgoing) = outgoing := by
  simp [toOrientedPDCode]

/-- The half-edge in a crossing slot is the corresponding end of the Gauss visit occupying that
slot. -/
@[simp]
theorem toOrientedPDCode_crossing (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    D.toOrientedPDCode.crossing c slot =
      halfEdge (D.crossingVisit c slot) (D.crossingOutgoing c slot) := by
  rw [OrientedPDCode.crossing_apply, toOrientedPDCode, Equiv.trans_apply,
    Equiv.symm_apply_apply, crossingHalfEdgeEquiv_apply]

/-- The orientation at a crossing slot agrees with the incoming/outgoing direction extracted from
the Gauss code. -/
@[simp]
theorem toOrientedPDCode_orientation_crossing (D : BasedOrientedGaussCode n)
    (c : Fin n) (slot : Fin 4) :
    D.toOrientedPDCode.orientation (D.toOrientedPDCode.crossing c slot) =
      D.crossingOutgoing c slot := by
  rw [D.toOrientedPDCode_crossing, D.toOrientedPDCode_orientation_halfEdge]

/-- At a crossing of the converted PD-code, the over-strand is exactly the visit marked over by
the Gauss code. -/
@[simp]
theorem toOrientedPDCode_isOver_crossing (D : BasedOrientedGaussCode n)
    (c : Fin n) (slot : Fin 4) :
    D.toOrientedPDCode.isOver c slot = D.over (D.crossingVisit c slot) := by
  rw [D.over_crossingVisit]
  fin_cases slot <;> simp [toOrientedPDCode]

/-- The converted PD-code has exactly the crossing sign stored by the Gauss code. -/
@[simp]
theorem toOrientedPDCode_crossingSign (D : BasedOrientedGaussCode n) (c : Fin n) :
    D.toOrientedPDCode.crossingSign c = (D.sign c : ℤ) := by
  rcases Int.units_eq_one_or (D.sign c) with hsign | hsign
  · rw [hsign]
    apply (OrientedPDCode.crossingSign_eq_one_iff _ _).2
    rw [D.toOrientedPDCode_orientation_crossing, D.toOrientedPDCode_orientation_crossing,
      D.toOrientedPDCode_overPair]
    simp only [crossingOutgoing, hsign, ↓reduceIte]
    decide
  · rw [hsign]
    apply (OrientedPDCode.crossingSign_eq_neg_one_iff _ _).2
    rw [D.toOrientedPDCode_orientation_crossing, D.toOrientedPDCode_orientation_crossing,
      D.toOrientedPDCode_overPair]
    have hne : D.sign c ≠ 1 := hsign ▸ (by decide)
    simp only [crossingOutgoing, hne, ↓reduceIte]
    decide

end BasedOrientedGaussCode

end TauCeti
