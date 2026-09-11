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
* `TauCeti.visitHalfEdgeEquiv` labels the incoming and outgoing half-edges of a prescribed number of
  visits.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode` converts a based oriented Gauss code to an
  oriented PD-code.
* `TauCeti.FramedBasedOrientedGaussCode.toFramedOrientedPDCode` is the framed refinement.

## Main results

* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_edgePair_visitHalfEdge` says that the output
  follows the traversal order.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_isOver_crossing` identifies the PD over-strand
  with the over visit of the Gauss code.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_crossingSign` proves preservation of crossing
  signs.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_writhe` proves agreement of the two writhes.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_injective` proves that the conversion loses no
  Gauss-code data.
-/

public section

namespace TauCeti

/-- The standard equivalence enumerating the incoming and outgoing half-edges of `2 * n` visits. -/
def visitHalfEdgeEquiv (n : ℕ) : Fin (2 * n) × Bool ≃ Fin (4 * n) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans <|
    finProdFinEquiv.trans (finCongr (by omega))

/-- The visit-half-edge equivalence numbers the incoming end of visit `i` by `2 * i` and its
outgoing end by `2 * i + 1`. -/
@[simp]
theorem visitHalfEdgeEquiv_apply (n : ℕ) (i : Fin (2 * n)) (outgoing : Bool) :
    (visitHalfEdgeEquiv n (i, outgoing)).val = 2 * i.val + outgoing.toNat := by
  cases outgoing <;>
    simp [visitHalfEdgeEquiv, finTwoEquiv, finProdFinEquiv, Nat.add_comm]

namespace BasedOrientedGaussCode

variable {n : ℕ}

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
private def negativeSlotEquiv : Fin 4 ≃ Bool × Bool :=
  (Equiv.swap (1 : Fin 4) 3).trans positiveSlotEquiv

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
    fin_cases slot <;>
      simp [slotEquiv, negativeSlotEquiv, Equiv.swap_apply_def, positiveSlotEquiv, hne]

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
    fin_cases slot <;>
      simp [crossingOutgoing, slotEquiv, negativeSlotEquiv, Equiv.swap_apply_def,
        positiveSlotEquiv, h, hne]

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

/-- Opposite slots at a crossing belong to the same Gauss-code visit. -/
@[simp]
theorem crossingVisit_oppositeCrossingSlot (D : BasedOrientedGaussCode n) (c : Fin n)
    (slot : Fin 4) :
    D.crossingVisit c (PDCode.oppositeCrossingSlot slot) = D.crossingVisit c slot := by
  apply D.visitDataEquiv.injective
  simp only [visitDataEquiv_apply, visit_crossingVisit, over_crossingVisit]
  congr 1
  have hopposite : PDCode.oppositeCrossingSlot slot = slot + 2 := by
    apply Fin.ext
    exact PDCode.oppositeCrossingSlot_apply slot
  rw [hopposite]
  fin_cases slot <;> decide

/-- Opposite slots at a crossing have opposite incoming/outgoing directions. -/
@[simp]
theorem crossingOutgoing_oppositeCrossingSlot (D : BasedOrientedGaussCode n) (c : Fin n)
    (slot : Fin 4) :
    D.crossingOutgoing c (PDCode.oppositeCrossingSlot slot) = !D.crossingOutgoing c slot := by
  rw [← slotEquiv_snd D c (PDCode.oppositeCrossingSlot slot), ← slotEquiv_snd D c slot]
  exact slotEquiv_snd_opposite (D.sign c) slot

/-- Relabelling a crossing transports the visit occupying each of its slots. -/
@[simp]
theorem crossingVisit_relabel (D : BasedOrientedGaussCode n) (e : Equiv.Perm (Fin n))
    (c : Fin n) (slot : Fin 4) :
    (D.relabel e).crossingVisit c slot = D.crossingVisit (e.symm c) slot := by
  apply (D.relabel e).visitDataEquiv.injective
  apply Prod.ext
  · simp only [visitDataEquiv_apply, visit_relabel]
    calc
      e (D.visit ((D.relabel e).crossingVisit c slot)) = c := by
        simpa only [visit_relabel] using (D.relabel e).visit_crossingVisit c slot
      _ = e (D.visit (D.crossingVisit (e.symm c) slot)) := by simp
  · simp only [visitDataEquiv_apply]
    simp

/-- Relabelling a crossing transports the incoming/outgoing data at each of its slots. -/
@[simp]
theorem crossingOutgoing_relabel (D : BasedOrientedGaussCode n) (e : Equiv.Perm (Fin n))
    (c : Fin n) (slot : Fin 4) :
    (D.relabel e).crossingOutgoing c slot = D.crossingOutgoing (e.symm c) slot := by
  simp [crossingOutgoing]

/-- At each crossing, the four slots are equivalent to an over/under visit and an
incoming/outgoing end of that visit. -/
private def crossingSlotDataEquiv (D : BasedOrientedGaussCode n) :
    Fin n × Fin 4 ≃ (Fin n × Bool) × Bool :=
  (Equiv.prodCongrRight fun c : Fin n => slotEquiv (D.sign c)).trans
    (Equiv.prodAssoc (Fin n) Bool Bool).symm

/-!
### Half-edges and traversal
-/

/-- On visit ends, arc pairing joins an outgoing half-edge to the incoming half-edge of the next
visit, and conversely joins an incoming half-edge to the outgoing half-edge of the previous visit.
-/
private def traversalEdge (n : ℕ) (p : Fin (2 * n) × Bool) : Fin (2 * n) × Bool :=
  if p.2 then (finRotate _ p.1, false) else ((finRotate _).symm p.1, true)

private theorem traversalEdge_involutive (n : ℕ) : Function.Involutive (traversalEdge n) := by
  rintro ⟨i, outgoing⟩
  cases outgoing
  · exact Prod.ext (Equiv.apply_symm_apply (finRotate _) i) rfl
  · exact Prod.ext (Equiv.symm_apply_apply (finRotate _) i) rfl

private def traversalEdgePerm (n : ℕ) : Equiv.Perm (Fin (2 * n) × Bool) :=
  Function.Involutive.toPerm _ (traversalEdge_involutive n)

/-- Arc pairing on visit ends is a perfect matching. -/
private def traversalEdgePair (n : ℕ) : PerfectMatching (Fin (2 * n) × Bool) :=
  PerfectMatching.mk (traversalEdgePerm n)
    (fun p => (traversalEdgePerm n).left_inv p)
    (by rintro ⟨i, outgoing⟩ h; cases outgoing <;> simp [traversalEdgePerm, traversalEdge] at h)

/-- The permutation that places the four crossing slots into the half-edge enumeration induced by
the Gauss traversal. -/
private noncomputable def crossingHalfEdgeEquiv (D : BasedOrientedGaussCode n) :
    Fin n × Fin 4 ≃ Fin (4 * n) :=
  (crossingSlotDataEquiv D).trans <|
    (Equiv.prodCongr D.visitDataEquiv.symm (Equiv.refl Bool)).trans
      (visitHalfEdgeEquiv n)

private theorem crossingHalfEdgeEquiv_apply (D : BasedOrientedGaussCode n)
    (c : Fin n) (slot : Fin 4) :
    crossingHalfEdgeEquiv D (c, slot) =
      visitHalfEdgeEquiv n (D.crossingVisit c slot, D.crossingOutgoing c slot) := by
  simp [crossingHalfEdgeEquiv, crossingSlotDataEquiv, crossingVisit,
    slotEquiv_fst, slotEquiv_snd]

/-!
### Conversion to a PD-code
-/

/-- Convert a based oriented Gauss code into an oriented PD-code. The chosen base point is used
only to number the visits; forgetting the half-edge labels forgets that choice. -/
noncomputable def toOrientedPDCode (D : BasedOrientedGaussCode n) : OrientedPDCode n where
  halfEdge := (PDCode.crossingSlotEquiv n).symm.trans (crossingHalfEdgeEquiv D)
  edgePair := PerfectMatching.congr (visitHalfEdgeEquiv n) (traversalEdgePair n)
  crossinglessComponentCount := if n = 0 then 1 else 0
  overPair := fun _ => false
  orientation := fun h => ((visitHalfEdgeEquiv n).symm h).2
  orientation_edgePair := by
    intro h
    rw [PerfectMatching.congr_val_apply]
    obtain ⟨i, outgoing⟩ := (visitHalfEdgeEquiv n).symm h
    rw [Equiv.symm_apply_apply]
    cases outgoing <;> simp [traversalEdgePair, traversalEdgePerm, traversalEdge]
  orientation_oppositeCrossingSlot := by
    intro c slot
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, crossingHalfEdgeEquiv_apply]
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

/-- In the zero-crossing case, the crossing-free component uses the convention represented by
`true`. -/
@[simp]
theorem toOrientedPDCode_crossinglessComponents (D : BasedOrientedGaussCode n) :
    D.toOrientedPDCode.crossinglessComponents = if n = 0 then {true} else 0 := (rfl)

/-- The conversion sends the crossing-free Gauss code to the `true`-oriented crossing-free unknot,
not to the empty link. -/
@[simp]
theorem toOrientedPDCode_empty :
    (empty : BasedOrientedGaussCode 0).toOrientedPDCode = orientedPDCodeUnknot true := by
  calc
    _ = orientedPDCodeUnlink
        (empty : BasedOrientedGaussCode 0).toOrientedPDCode.crossinglessComponents :=
      orientedPDCode_eq_unlink _
    _ = orientedPDCodeUnlink {true} := by simp
    _ = orientedPDCodeUnknot true := by
      simpa only [orientedPDCodeUnknot_crossinglessComponents] using
        (orientedPDCode_eq_unlink (orientedPDCodeUnknot true)).symm

private theorem toOrientedPDCode_edgePair_outgoing_aux (D : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) :
    D.toOrientedPDCode.edgePair.val (visitHalfEdgeEquiv n (i, true)) =
      visitHalfEdgeEquiv n (finRotate _ i, false) := by
  simp [toOrientedPDCode, traversalEdgePair, traversalEdgePerm, traversalEdge]

/-- Arc pairing follows the cyclic traversal, changing an outgoing end to the next incoming end
and an incoming end to the previous outgoing end. -/
@[simp]
theorem toOrientedPDCode_edgePair_visitHalfEdge (D : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) (outgoing : Bool) :
    D.toOrientedPDCode.edgePair.val (visitHalfEdgeEquiv n (i, outgoing)) =
      visitHalfEdgeEquiv n
        (if outgoing then (finRotate _ i, false) else ((finRotate _).symm i, true)) := by
  cases outgoing
  · apply D.toOrientedPDCode.edgePair.apply_eq_of_apply_eq
    have h := D.toOrientedPDCode_edgePair_outgoing_aux ((finRotate _).symm i)
    rwa [(finRotate _).apply_symm_apply] at h
  · exact D.toOrientedPDCode_edgePair_outgoing_aux i

/-- The direction decoration remembers which half-edge of a visit is outgoing. -/
@[simp]
theorem toOrientedPDCode_orientation_halfEdge (D : BasedOrientedGaussCode n)
    (i : Fin (2 * n)) (outgoing : Bool) :
    D.toOrientedPDCode.orientation (visitHalfEdgeEquiv n (i, outgoing)) = outgoing := by
  simp [toOrientedPDCode]

/-- The half-edge in a crossing slot is the corresponding end of the Gauss visit occupying that
slot. -/
@[simp]
theorem toOrientedPDCode_crossing (D : BasedOrientedGaussCode n) (c : Fin n) (slot : Fin 4) :
    D.toOrientedPDCode.halfEdge (PDCode.crossingSlotEquiv n (c, slot)) =
      visitHalfEdgeEquiv n (D.crossingVisit c slot, D.crossingOutgoing c slot) := by
  rw [toOrientedPDCode, Equiv.trans_apply, Equiv.symm_apply_apply,
    crossingHalfEdgeEquiv_apply]

/-- Converting a relabelled Gauss code relabels the crossing blocks of the resulting PD-code
while leaving its traversal-based half-edge labels fixed. -/
@[simp]
theorem toOrientedPDCode_relabel (D : BasedOrientedGaussCode n) (e : Equiv.Perm (Fin n)) :
    (D.relabel e).toOrientedPDCode =
      D.toOrientedPDCode.relabel (Equiv.refl (Fin (4 * n))) e := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · apply Equiv.ext
      intro h
      rw [← (PDCode.crossingSlotEquiv n).apply_symm_apply h]
      rcases (PDCode.crossingSlotEquiv n).symm h with ⟨c, slot⟩
      rw [toOrientedPDCode_crossing, OrientedPDCode.relabel_halfEdge]
      simp only [Equiv.equivCongr_apply_apply, Equiv.refl_apply,
        PDCode.crossingBlockPerm_symm_apply_crossingSlotEquiv, toOrientedPDCode_crossing,
        crossingVisit_relabel, crossingOutgoing_relabel, visitHalfEdgeEquiv]
    · rw [OrientedPDCode.relabel_edgePair]
      simp [toOrientedPDCode, visitHalfEdgeEquiv]
    · simp [toOrientedPDCode]
    · funext c
      simp [toOrientedPDCode]
  · funext h
    simp [toOrientedPDCode, visitHalfEdgeEquiv, OrientedPDCode.relabel_orientation]
  · simp [toOrientedPDCode]

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
    rw [OrientedPDCode.crossing_apply, OrientedPDCode.crossing_apply,
      D.toOrientedPDCode_crossing, D.toOrientedPDCode_orientation_halfEdge,
      D.toOrientedPDCode_crossing, D.toOrientedPDCode_orientation_halfEdge,
      D.toOrientedPDCode_overPair]
    simp only [crossingOutgoing, hsign, ↓reduceIte]
    decide
  · rw [hsign]
    apply (OrientedPDCode.crossingSign_eq_neg_one_iff _ _).2
    rw [OrientedPDCode.crossing_apply, OrientedPDCode.crossing_apply,
      D.toOrientedPDCode_crossing, D.toOrientedPDCode_orientation_halfEdge,
      D.toOrientedPDCode_crossing, D.toOrientedPDCode_orientation_halfEdge,
      D.toOrientedPDCode_overPair]
    have hne : D.sign c ≠ 1 := hsign ▸ (by decide)
    simp only [crossingOutgoing, hne, ↓reduceIte]
    decide

/-- The two writhes agree. -/
@[simp]
theorem toOrientedPDCode_writhe (D : BasedOrientedGaussCode n) :
    D.toOrientedPDCode.writhe = D.writhe := by
  simp [OrientedPDCode.writhe_def, writhe_def]

/-- The conversion to oriented PD-codes is injective: the crossing-incidence data remembers the
visit sequence, the over/under data, and the crossing signs of the Gauss code. -/
theorem toOrientedPDCode_injective : Function.Injective (toOrientedPDCode (n := n)) := by
  intro D E h
  have hvisit (c : Fin n) (slot : Fin 4) : D.crossingVisit c slot = E.crossingVisit c slot := by
    have hhalf := congrArg
      (fun C : OrientedPDCode n => C.halfEdge (PDCode.crossingSlotEquiv n (c, slot))) h
    simp only [toOrientedPDCode_crossing] at hhalf
    exact congrArg Prod.fst ((visitHalfEdgeEquiv n).injective hhalf)
  have hsymm : D.visitDataEquiv.symm = E.visitDataEquiv.symm := by
    refine Equiv.ext fun ⟨c, over⟩ => ?_
    cases over
    · simpa [crossingVisit] using hvisit c 1
    · simpa [crossingVisit] using hvisit c 0
  have hequiv : D.visitDataEquiv = E.visitDataEquiv := by
    simpa using congrArg Equiv.symm hsymm
  apply BasedOrientedGaussCode.ext
  · funext i
    simpa using congrArg (fun e => (e i).1) hequiv
  · funext i
    simpa using congrArg (fun e => (e i).2) hequiv
  · funext c
    apply Units.ext
    simpa using congrArg (fun C : OrientedPDCode n => C.crossingSign c) h

end BasedOrientedGaussCode

namespace FramedBasedOrientedGaussCode

variable {n : ℕ}

/-- The framed oriented PD-code of a framed based oriented Gauss code. A Gauss code traverses a
single component, so its one framing coefficient is the framing of every crossing visit. -/
noncomputable def toFramedOrientedPDCode (D : FramedBasedOrientedGaussCode n) :
    FramedOrientedPDCode n where
  toOrientedPDCode := D.forgetFraming.toOrientedPDCode
  framing _ := D.framing
  framing_edgePair _ := (rfl)
  framing_oppositeCrossingSlot _ _ := (rfl)
  crossinglessFramings := if n = 0 then {(true, D.framing)} else 0
  crossinglessFramings_map_fst := by
    by_cases h : n = 0 <;>
      simp [h, BasedOrientedGaussCode.toOrientedPDCode]

/-- Forgetting the framing commutes with passing to PD-codes. -/
@[simp] theorem toFramedOrientedPDCode_toOrientedPDCode (D : FramedBasedOrientedGaussCode n) :
    D.toFramedOrientedPDCode.toOrientedPDCode = D.forgetFraming.toOrientedPDCode := (rfl)

/-- Every crossing visit of a framed code carries the single framing coefficient. -/
@[simp] theorem toFramedOrientedPDCode_framing (D : FramedBasedOrientedGaussCode n)
    (h : Fin (4 * n)) : D.toFramedOrientedPDCode.framing h = D.framing := (rfl)

/-- A crossing-free framed code carries the Gauss code's framing on its unique component, while
a code with crossings has no crossing-free components. -/
@[simp] theorem toFramedOrientedPDCode_crossinglessFramings
    (D : FramedBasedOrientedGaussCode n) :
    D.toFramedOrientedPDCode.crossinglessFramings =
      if n = 0 then {(true, D.framing)} else 0 := (rfl)

end FramedBasedOrientedGaussCode

end TauCeti

