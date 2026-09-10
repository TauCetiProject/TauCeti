/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode
public import TauCeti.KnotTheory.PDCode
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

/-!
# From based oriented Gauss codes to oriented PD-codes

A based oriented Gauss code records a diagram by walking along the knot from a base point: it
lists the crossing seen at each of the `2 * n` visits, which strand is over there, and the sign
of each crossing. An oriented PD-code instead records the local incidence data at each crossing:
the four half-edges in slot order, which opposite pair of slots is the over strand, and the
directions of the half-edges, from which the crossing sign is *derived*. This file builds the
map from the first presentation to the second.

The construction reads the half-edges off the traversal: visit `v` is entered by one half-edge
and left by another, the arcs of the diagram join the half-edge leaving `v` to the half-edge
entering the next visit, and the four half-edges at a crossing are the two at each of its two
visits. The two slot pairs `{0, 2}` and `{1, 3}` are the strands of the first and of the second
visit to the crossing, so `overPair` is exactly the over/under datum at the second visit. The
crossing sign is *not* stored by a PD-code, so it has to be encoded in the slot order: which of
the two half-edges of the second visit occupies slot `1` is chosen so that the sign the PD-code
derives is the sign the Gauss code records
(`TauCeti.BasedOrientedGaussCode.toOrientedPDCode_crossingSign`).

Neither presentation imposes planarity, so this is a correspondence of codes, not a statement
that either side is realised by a drawing in the plane. The map is injective, so the passage
from a traversal to crossing-incidence data loses nothing.

The two presentations carry *different* normal forms for the mirror image: a Gauss code is
mirrored by negating every sign, keeping the over/under data (reflection in a plane transverse
to the diagram), while a PD-code is mirrored by exchanging the two strands at every crossing
(reflection in the plane of the diagram). Both negate every crossing sign, and both therefore
negate the writhe, but they are not the same map on codes, so `toOrientedPDCode` intertwines
them only up to the slot order at each crossing.

Conventions follow W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapter 1, as
in the two files this one joins.

## Main definitions

* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode`: the oriented PD-code of a based oriented
  Gauss code.
* `TauCeti.FramedBasedOrientedGaussCode.toFramedOrientedPDCode`: the framed refinement.

## Main results

* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_crossingSign`: the sign a PD-code derives
  from its slot order is the sign the Gauss code records.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_writhe`: the two writhes agree.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_injective`: the map is injective.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_isOver_one` and
  `toOrientedPDCode_isOver_zero`: the over and under strands of a crossing are the strands of the
  visits the Gauss code records as over and as under.
-/

public section

namespace TauCeti

namespace BasedOrientedGaussCode

/-- The half-edges of an `n`-crossing code, indexed by a visit of the traversal together with a
direction: `(v, false)` is the half-edge entering the crossing at visit `v` and `(v, true)` is
the half-edge leaving it. -/
private def halfEdgeEquiv (n : ℕ) : Fin (2 * n) × Bool ≃ Fin (4 * n) :=
  ((Equiv.refl (Fin (2 * n))).prodCongr finTwoEquiv.symm).trans
    (finProdFinEquiv.trans (finCongr (by ring)))

/-- Read a crossing slot as a pair of Booleans: whether the slot lies on the strand of the
second visit to the crossing, and whether its half-edge leaves the crossing. The parameter `b`
is the direction of slot `1`, which is what a PD-code uses to record the crossing sign. -/
private def slotSplit (b : Bool) : Fin 4 ≃ Bool × Bool where
  toFun := ![(false, false), (true, b), (false, true), (true, !b)]
  invFun p := if p.1 then (if p.2 = b then 1 else 3) else (if p.2 then 2 else 0)
  left_inv s := by fin_cases s <;> cases b <;> decide
  right_inv p := by obtain ⟨x, y⟩ := p; cases x <;> cases y <;> cases b <;> decide

/-- Slot `0` enters the crossing along the strand of its first visit. -/
@[simp] private theorem slotSplit_zero (b : Bool) : slotSplit b 0 = (false, false) := (rfl)

/-- Slot `1` lies on the strand of the second visit, with the recorded direction. -/
@[simp] private theorem slotSplit_one (b : Bool) : slotSplit b 1 = (true, b) := (rfl)

/-- Slot `2` leaves the crossing along the strand of its first visit. -/
@[simp] private theorem slotSplit_two (b : Bool) : slotSplit b 2 = (false, true) := (rfl)

/-- Slot `3` lies on the strand of the second visit, opposite to slot `1`. -/
@[simp] private theorem slotSplit_three (b : Bool) : slotSplit b 3 = (true, !b) := (rfl)

/-- The two slots of a strand carry opposite directions: one enters the crossing and the other
leaves it. -/
@[simp] private theorem slotSplit_snd_oppositeCrossingSlot (b : Bool) (s : Fin 4) :
    (slotSplit b (PDCode.oppositeCrossingSlot s)).2 = !(slotSplit b s).2 := by
  have h : ∀ t : Fin 4, PDCode.oppositeCrossingSlot t = t + 2 := fun t =>
    Fin.eq_of_val_eq (PDCode.oppositeCrossingSlot_apply t)
  fin_cases s <;> rw [h] <;> cases b <;> exact (rfl)

/-- Following an arc of the diagram: the half-edge leaving a visit is joined to the half-edge
entering the next visit along the traversal, cyclically. -/
private def visitArcMap (m : ℕ) : Fin m × Bool → Fin m × Bool
  | (v, true) => (finRotate m v, false)
  | (v, false) => ((finRotate m).symm v, true)

/-- Following an arc exchanges entering and leaving a crossing. -/
@[simp] private theorem visitArcMap_snd (m : ℕ) (p : Fin m × Bool) :
    (visitArcMap m p).2 = !p.2 := by
  obtain ⟨v, b⟩ := p
  cases b <;> simp [visitArcMap]

/-- Following an arc from either of its ends returns to the other. -/
private theorem visitArcMap_involutive (m : ℕ) : Function.Involutive (visitArcMap m) := by
  rintro ⟨v, b⟩
  cases b <;>
    simp only [visitArcMap, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The arcs of a based traversal of `m` visits, as a perfect matching of the half-edges. -/
private def visitArcMatching (m : ℕ) : PerfectMatching (Fin m × Bool) :=
  ⟨Function.Involutive.toPerm _ (visitArcMap_involutive m),
    isPerfectMatching_iff.mpr ⟨visitArcMap_involutive m, by
      intro p hp
      have h2 : (visitArcMap m p).2 = p.2 := congrArg Prod.snd hp
      rw [visitArcMap_snd] at h2
      exact Bool.not_ne_self _ h2⟩⟩

/-- The matching of arcs is given by following an arc. -/
@[simp] private theorem visitArcMatching_val (m : ℕ) (p : Fin m × Bool) :
    (visitArcMatching m).val p = visitArcMap m p := (rfl)

variable {n : ℕ} (D : BasedOrientedGaussCode n)

/-- The direction to give to slot `1` of a crossing: it agrees with the over/under datum of the
second visit exactly when the crossing is positive. This is the choice that makes the sign
derived from the PD-code equal the sign recorded by the Gauss code. -/
private noncomputable def slotOneDirection (i : Fin n) : Bool :=
  if D.sign i = 1 then D.over (D.visitAt i true) else !D.over (D.visitAt i true)

/-- The direction of slot `1` agrees with the over/under datum of the second visit exactly at a
positive crossing. -/
private theorem slotOneDirection_eq_over_iff (i : Fin n) :
    D.slotOneDirection i = D.over (D.visitAt i true) ↔ D.sign i = 1 := by
  unfold slotOneDirection
  split <;> simp_all

/-- The half-edge in slot `s` of crossing `i`, as a visit together with a direction. -/
private noncomputable def slotEquiv : Fin n × Fin 4 ≃ Fin (2 * n) × Bool :=
  (Equiv.sigmaEquivProd (Fin n) (Fin 4)).symm.trans
    (((Equiv.sigmaCongrRight fun i => slotSplit (D.slotOneDirection i)).trans
        (Equiv.sigmaEquivProd (Fin n) (Bool × Bool))).trans
      ((Equiv.prodAssoc (Fin n) Bool Bool).symm.trans
        (D.visitEquiv.symm.prodCongr (Equiv.refl Bool))))

/-- The half-edge in a slot is read off the visit and direction that slot records. -/
@[simp] private theorem slotEquiv_apply (i : Fin n) (s : Fin 4) :
    D.slotEquiv (i, s) =
      (D.visitAt i (slotSplit (D.slotOneDirection i) s).1,
        (slotSplit (D.slotOneDirection i) s).2) := by
  apply Prod.ext
  · apply D.visitEquiv.injective
    simp [slotEquiv]
  · rfl

/-- The oriented PD-code of a based oriented Gauss code.

Slots `0` and `2` at a crossing are the strand of its first visit and slots `1` and `3` the
strand of its second, so `overPair` is the over/under datum at the second visit; the direction
of slot `1` encodes the crossing sign. A code with no crossings is the single crossing-free
circle the traversal walks, recorded with the reference orientation. -/
noncomputable def toOrientedPDCode : OrientedPDCode n where
  halfEdge := (PDCode.crossingSlotEquiv n).symm.trans (D.slotEquiv.trans (halfEdgeEquiv n))
  edgePair := PerfectMatching.congr (halfEdgeEquiv n) (visitArcMatching (2 * n))
  crossinglessComponentCount := if n = 0 then 1 else 0
  overPair i := D.over (D.visitAt i true)
  orientation h := ((halfEdgeEquiv n).symm h).2
  orientation_edgePair := by
    intro h
    rw [PerfectMatching.congr_val_apply, Equiv.symm_apply_apply, visitArcMatching_val,
      visitArcMap_snd]
  orientation_oppositeCrossingSlot := by
    intro i slot
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, slotEquiv_apply,
      slotSplit_snd_oppositeCrossingSlot]
  crossinglessComponents := if n = 0 then {true} else 0
  crossinglessComponents_card := by
    by_cases h : n = 0 <;> simp [h]

/-- The over strand of a crossing is the strand of its second visit exactly when the Gauss
code records that visit as over. -/
@[simp] theorem toOrientedPDCode_overPair (i : Fin n) :
    D.toOrientedPDCode.overPair i = D.over (D.visitAt i true) := (rfl)

/-- A code with a crossing has no crossing-free component, while a crossing-free code is the
single circle its traversal walks. -/
@[simp] theorem toOrientedPDCode_crossinglessComponents :
    D.toOrientedPDCode.crossinglessComponents = if n = 0 then {true} else 0 := (rfl)

/-- The half-edges of the PD-code are the ones the slot assignment names. -/
private theorem toOrientedPDCode_halfEdge (i : Fin n) (s : Fin 4) :
    D.toOrientedPDCode.halfEdge (PDCode.crossingSlotEquiv n (i, s)) =
      halfEdgeEquiv n (D.slotEquiv (i, s)) := by
  simp [toOrientedPDCode]

/-- The half-edge in slot `s` of crossing `i` is the one at the visit that slot belongs to,
carrying the direction that slot records. -/
private theorem toOrientedPDCode_crossing_raw (i : Fin n) (s : Fin 4) :
    D.toOrientedPDCode.crossing i s =
      halfEdgeEquiv n
        (D.visitAt i (slotSplit (D.slotOneDirection i) s).1,
          (slotSplit (D.slotOneDirection i) s).2) := by
  rw [OrientedPDCode.crossing_apply, toOrientedPDCode_halfEdge, slotEquiv_apply]

private noncomputable def slotAtVisit (v : Fin (2 * n)) (outgoing : Bool) : Fin 4 :=
  if D.isSecondVisit v then
    if D.slotOneDirection (D.visit v) = outgoing then 1 else 3
  else if outgoing then 2 else 0

private theorem slotSplit_slotAtVisit (v : Fin (2 * n)) (outgoing : Bool) :
    slotSplit (D.slotOneDirection (D.visit v)) (D.slotAtVisit v outgoing) =
      (D.isSecondVisit v, outgoing) := by
  cases hv : D.isSecondVisit v <;> cases hd : D.slotOneDirection (D.visit v) <;>
    cases outgoing <;> simp [slotAtVisit, hv, hd]

private theorem toOrientedPDCode_crossing_slotAtVisit (v : Fin (2 * n)) (outgoing : Bool) :
    D.toOrientedPDCode.crossing (D.visit v) (D.slotAtVisit v outgoing) =
      halfEdgeEquiv n (v, outgoing) := by
  rw [toOrientedPDCode_crossing_raw, slotSplit_slotAtVisit, visitAt_visit]

private theorem toOrientedPDCode_edgePair_raw (v : Fin (2 * n)) :
    D.toOrientedPDCode.edgePair.val (halfEdgeEquiv n (v, true)) =
      halfEdgeEquiv n (finRotate (2 * n) v, false) := by
  have h : D.toOrientedPDCode.edgePair =
      PerfectMatching.congr (halfEdgeEquiv n) (visitArcMatching (2 * n)) := (rfl)
  rw [h, PerfectMatching.congr_val_apply_apply, visitArcMatching_val]
  rfl

private theorem toOrientedPDCode_orientation_crossing_raw (i : Fin n) (s : Fin 4) :
    D.toOrientedPDCode.orientation (D.toOrientedPDCode.crossing i s) =
      (slotSplit (D.slotOneDirection i) s).2 := by
  simp [toOrientedPDCode]

/-- The directions in the four crossing slots are the ones determined by the traversal and the
recorded crossing sign. -/
theorem toOrientedPDCode_orientation_crossing (i : Fin n) (s : Fin 4) :
    D.toOrientedPDCode.orientation (D.toOrientedPDCode.crossing i s) =
      ![false,
        if D.sign i = 1 then D.over (D.visitAt i true) else !D.over (D.visitAt i true),
        true,
        !(if D.sign i = 1 then D.over (D.visitAt i true) else !D.over (D.visitAt i true))] s := by
  rw [toOrientedPDCode_orientation_crossing_raw]
  fin_cases s <;> simp [slotOneDirection]

/-- The crossing slot selected by a visit and a direction has that direction. -/
theorem toOrientedPDCode_crossing (v : Fin (2 * n)) (outgoing : Bool) :
    let b := if D.sign (D.visit v) = 1 then D.over (D.visitAt (D.visit v) true)
      else !D.over (D.visitAt (D.visit v) true)
    let s : Fin 4 := if D.isSecondVisit v then
      if b = outgoing then 1 else 3
    else if outgoing then 2 else 0
    D.toOrientedPDCode.orientation (D.toOrientedPDCode.crossing (D.visit v) s) = outgoing := by
  -- Fold the expanded public formula back to the private slot selector used by the construction.
  change D.toOrientedPDCode.orientation
    (D.toOrientedPDCode.crossing (D.visit v) (D.slotAtVisit v outgoing)) = outgoing
  rw [toOrientedPDCode_crossing_slotAtVisit]
  simp [toOrientedPDCode]

/-- The arcs of the diagram join the half-edge leaving a visit to the half-edge entering the
next visit along the traversal. -/
theorem toOrientedPDCode_edgePair (v : Fin (2 * n)) :
    let slotAt := fun (w : Fin (2 * n)) (outgoing : Bool) =>
      let b := if D.sign (D.visit w) = 1 then D.over (D.visitAt (D.visit w) true)
        else !D.over (D.visitAt (D.visit w) true)
      (if D.isSecondVisit w then
        if b = outgoing then 1 else 3
      else if outgoing then 2 else 0 : Fin 4)
    D.toOrientedPDCode.edgePair.val
        (D.toOrientedPDCode.crossing (D.visit v) (slotAt v true)) =
      D.toOrientedPDCode.crossing (D.visit (finRotate (2 * n) v))
        (slotAt (finRotate (2 * n) v) false) := by
  -- Fold the expanded public formula back to the private slot selector used by the construction.
  change D.toOrientedPDCode.edgePair.val
      (D.toOrientedPDCode.crossing (D.visit v) (D.slotAtVisit v true)) =
    D.toOrientedPDCode.crossing (D.visit (finRotate (2 * n) v))
      (D.slotAtVisit (finRotate (2 * n) v) false)
  rw [toOrientedPDCode_crossing_slotAtVisit, toOrientedPDCode_edgePair_raw,
    toOrientedPDCode_crossing_slotAtVisit]

/-- The over strand of a crossing of the PD-code is the strand of the visit the Gauss code
records as over. -/
theorem toOrientedPDCode_isOver_one (i : Fin n) :
    D.toOrientedPDCode.toPDCode.isOver i 1 = D.over (D.visitAt i true) := by
  simp

/-- The under strand of a crossing of the PD-code is the strand of the visit the Gauss code
records as under. -/
theorem toOrientedPDCode_isOver_zero (i : Fin n) :
    D.toOrientedPDCode.toPDCode.isOver i 0 = D.over (D.visitAt i false) := by
  have h := D.over_visitAt_not i true
  simp only [Bool.not_true] at h
  rw [PDCode.isOver_zero, toOrientedPDCode_overPair, h]

/-- **The signs agree**: the sign the PD-code derives from its slot order at a crossing is the
sign the Gauss code records there. -/
@[simp] theorem toOrientedPDCode_crossingSign (i : Fin n) :
    D.toOrientedPDCode.crossingSign i = (D.sign i : ℤ) := by
  have hpos : D.toOrientedPDCode.crossingSign i = 1 ↔ D.sign i = 1 := by
    rw [OrientedPDCode.crossingSign_eq_one_iff]
    rw [toOrientedPDCode_orientation_crossing, toOrientedPDCode_orientation_crossing,
      toOrientedPDCode_overPair]
    simp
  rcases Int.units_eq_one_or (D.sign i) with h | h
  · rw [hpos.mpr h, h]
    rfl
  · have hne : D.toOrientedPDCode.crossingSign i ≠ 1 := by
      intro hc
      rw [hpos.mp hc] at h
      exact absurd h (by simp [Units.ext_iff])
    rcases D.toOrientedPDCode.crossingSign_eq_one_or_neg_one i with h' | h'
    · exact absurd h' hne
    · rw [h', h]
      rfl

/-- The two writhes agree. -/
@[simp] theorem toOrientedPDCode_writhe : D.toOrientedPDCode.writhe = D.writhe := by
  simp [OrientedPDCode.writhe_def, writhe_def]

/-- The map to oriented PD-codes is injective: the crossing-incidence data remembers the whole
traversal. -/
theorem toOrientedPDCode_injective :
    Function.Injective (toOrientedPDCode (n := n)) := by
  intro D E h
  have hslot : ∀ (i : Fin n) (s : Fin 4), D.slotEquiv (i, s) = E.slotEquiv (i, s) := by
    intro i s
    refine (halfEdgeEquiv n).injective ?_
    have := congrArg (fun C => C.halfEdge (PDCode.crossingSlotEquiv n (i, s))) h
    rw [← D.toOrientedPDCode_halfEdge, ← E.toOrientedPDCode_halfEdge]
    exact this
  have hvisitAt : ∀ (i : Fin n) (s : Bool), D.visitAt i s = E.visitAt i s := by
    intro i s
    cases s
    · simpa using congrArg Prod.fst (hslot i 0)
    · simpa using congrArg Prod.fst (hslot i 1)
  have hdir : ∀ i : Fin n, D.slotOneDirection i = E.slotOneDirection i := by
    intro i
    simpa using congrArg Prod.snd (hslot i 1)
  have hequiv : D.visitEquiv = E.visitEquiv := by
    have : D.visitEquiv.symm = E.visitEquiv.symm := by
      apply Equiv.ext
      intro p
      calc
        D.visitEquiv.symm p = D.visitAt p.1 p.2 := by
          apply D.visitEquiv.injective
          simp
        _ = E.visitAt p.1 p.2 := hvisitAt p.1 p.2
        _ = E.visitEquiv.symm p := by
          apply E.visitEquiv.injective
          simp
    simpa using congrArg Equiv.symm this
  have hvisit : D.visit = E.visit := by
    funext v
    simpa using congrArg (fun e => (e v).1) hequiv
  have hovertrue : ∀ i : Fin n, D.over (D.visitAt i true) = E.over (E.visitAt i true) := by
    intro i
    simpa using congrArg (fun C => C.overPair i) h
  have hoverAt : ∀ (i : Fin n) (s : Bool), D.over (D.visitAt i s) = E.over (E.visitAt i s) := by
    intro i s
    cases s
    · have hD := D.over_visitAt_not i true
      have hE := E.over_visitAt_not i true
      simp only [Bool.not_true] at hD hE
      rw [hD, hE, hovertrue]
    · exact hovertrue i
  have hover : D.over = E.over := by
    funext v
    have hv : D.visitAt (D.visit v) (D.isSecondVisit v) = v := D.visitAt_visit v
    have hva := hoverAt (D.visit v) (D.isSecondVisit v)
    rw [hv, ← hvisitAt, hv] at hva
    exact hva
  have hsign : D.sign = E.sign := by
    funext i
    have hiff : D.sign i = 1 ↔ E.sign i = 1 := by
      rw [← D.slotOneDirection_eq_over_iff i, ← E.slotOneDirection_eq_over_iff i, hdir i,
        hvisitAt i true, hover]
    rcases Int.units_eq_one_or (D.sign i) with h₁ | h₁ <;>
      rcases Int.units_eq_one_or (E.sign i) with h₂ | h₂
    · rw [h₁, h₂]
    · rw [h₂] at hiff
      exact absurd (hiff.mp h₁) (by simp [Units.ext_iff])
    · rw [h₁] at hiff
      exact absurd (hiff.mpr h₂) (by simp [Units.ext_iff])
    · rw [h₁, h₂]
  exact ext hvisit hover hsign

/-- The crossing-free Gauss code is the crossing-free unknot diagram. -/
theorem toOrientedPDCode_empty :
    (empty : BasedOrientedGaussCode 0).toOrientedPDCode = orientedPDCodeUnknot true := by
  rw [orientedPDCode_eq_unlink (empty : BasedOrientedGaussCode 0).toOrientedPDCode,
    toOrientedPDCode_crossinglessComponents, orientedPDCodeUnknot_eq_unlink]
  simp

/-- The PD-code of the positive kink has writhe one. -/
theorem writhe_toOrientedPDCode_positiveKink :
    (positiveKink.toOrientedPDCode).writhe = 1 := by
  simp

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
