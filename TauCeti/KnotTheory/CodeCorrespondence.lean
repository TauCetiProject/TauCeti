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
the two half-edges of the second visit occupies slot `1` is chosen, in
`TauCeti.BasedOrientedGaussCode.slotOneDirection`, so that the sign the PD-code derives is the
sign the Gauss code records (`TauCeti.BasedOrientedGaussCode.crossingSign_toOrientedPDCode`).

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

* `TauCeti.BasedOrientedGaussCode.visitEquiv`: the two visits to a crossing, indexed by the
  crossing together with which of the two comes first along the traversal.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode`: the oriented PD-code of a based oriented
  Gauss code.
* `TauCeti.FramedBasedOrientedGaussCode.toFramedOrientedPDCode`: the framed refinement.

## Main results

* `TauCeti.BasedOrientedGaussCode.crossingSign_toOrientedPDCode`: the sign a PD-code derives
  from its slot order is the sign the Gauss code records.
* `TauCeti.BasedOrientedGaussCode.writhe_toOrientedPDCode`: the two writhes agree.
* `TauCeti.BasedOrientedGaussCode.toOrientedPDCode_injective`: the map is injective.
* `TauCeti.BasedOrientedGaussCode.isOver_toOrientedPDCode_one` and
  `isOver_toOrientedPDCode_zero`: the over and under strands of a crossing are the strands of
  the visits the Gauss code records as over and as under.
-/

public section

namespace TauCeti

namespace PDCode

/-- The half-edges of an `n`-crossing code, indexed by a visit of the traversal together with a
direction: `(v, false)` is the half-edge entering the crossing at visit `v` and `(v, true)` is
the half-edge leaving it. -/
def halfEdgeEquiv (n : ℕ) : Fin (2 * n) × Bool ≃ Fin (4 * n) :=
  ((Equiv.refl (Fin (2 * n))).prodCongr finTwoEquiv.symm).trans
    (finProdFinEquiv.trans (finCongr (by ring)))

/-- Read a crossing slot as a pair of Booleans: whether the slot lies on the strand of the
second visit to the crossing, and whether its half-edge leaves the crossing. The parameter `b`
is the direction of slot `1`, which is what a PD-code uses to record the crossing sign. -/
def slotSplit (b : Bool) : Fin 4 ≃ Bool × Bool where
  toFun := ![(false, false), (true, b), (false, true), (true, !b)]
  invFun p := if p.1 then (if p.2 = b then 1 else 3) else (if p.2 then 2 else 0)
  left_inv s := by fin_cases s <;> cases b <;> decide
  right_inv p := by obtain ⟨x, y⟩ := p; cases x <;> cases y <;> cases b <;> decide

/-- Slot `0` enters the crossing along the strand of its first visit. -/
@[simp] theorem slotSplit_zero (b : Bool) : slotSplit b 0 = (false, false) := (rfl)

/-- Slot `1` lies on the strand of the second visit, with the recorded direction. -/
@[simp] theorem slotSplit_one (b : Bool) : slotSplit b 1 = (true, b) := (rfl)

/-- Slot `2` leaves the crossing along the strand of its first visit. -/
@[simp] theorem slotSplit_two (b : Bool) : slotSplit b 2 = (false, true) := (rfl)

/-- Slot `3` lies on the strand of the second visit, opposite to slot `1`. -/
@[simp] theorem slotSplit_three (b : Bool) : slotSplit b 3 = (true, !b) := (rfl)

/-- The two slots of a strand carry opposite directions: one enters the crossing and the other
leaves it. -/
@[simp] theorem slotSplit_snd_oppositeCrossingSlot (b : Bool) (s : Fin 4) :
    (slotSplit b (oppositeCrossingSlot s)).2 = !(slotSplit b s).2 := by
  have h : ∀ t : Fin 4, oppositeCrossingSlot t = t + 2 := fun t =>
    Fin.eq_of_val_eq (oppositeCrossingSlot_apply t)
  fin_cases s <;> rw [h] <;> cases b <;> exact (rfl)

/-- Following an arc of the diagram: the half-edge leaving a visit is joined to the half-edge
entering the next visit along the traversal, cyclically. -/
def visitArcMap (m : ℕ) : Fin m × Bool → Fin m × Bool
  | (v, true) => (finRotate m v, false)
  | (v, false) => ((finRotate m).symm v, true)

/-- Following an arc exchanges entering and leaving a crossing. -/
@[simp] theorem visitArcMap_snd (m : ℕ) (p : Fin m × Bool) : (visitArcMap m p).2 = !p.2 := by
  obtain ⟨v, b⟩ := p
  cases b <;> simp [visitArcMap]

/-- Following an arc from either of its ends returns to the other. -/
theorem visitArcMap_involutive (m : ℕ) : Function.Involutive (visitArcMap m) := by
  rintro ⟨v, b⟩
  cases b <;>
    simp only [visitArcMap, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The arcs of a based traversal of `m` visits, as a perfect matching of the half-edges. -/
def visitArcMatching (m : ℕ) : PerfectMatching (Fin m × Bool) :=
  ⟨Function.Involutive.toPerm _ (visitArcMap_involutive m),
    isPerfectMatching_iff.mpr ⟨visitArcMap_involutive m, by
      intro p hp
      have h2 : (visitArcMap m p).2 = p.2 := congrArg Prod.snd hp
      rw [visitArcMap_snd] at h2
      exact Bool.not_ne_self _ h2⟩⟩

/-- The matching of arcs is given by following an arc. -/
@[simp] theorem visitArcMatching_val (m : ℕ) (p : Fin m × Bool) :
    (visitArcMatching m).val p = visitArcMap m p := (rfl)

end PDCode

namespace BasedOrientedGaussCode

variable {n : ℕ} (D : BasedOrientedGaussCode n)

/-- Whether a visit is the later of the two visits to its crossing. -/
def isSecondVisit (v : Fin (2 * n)) : Bool :=
  decide (D.partner.val v < v)

/-- Exactly one of the two visits to a crossing is the later one. -/
@[simp] theorem isSecondVisit_partner (v : Fin (2 * n)) :
    D.isSecondVisit (D.partner.val v) = !D.isSecondVisit v := by
  have hne : D.partner.val v ≠ v := D.partner.apply_ne v
  simp only [isSecondVisit, PerfectMatching.apply_apply]
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, asymm h]
  · simp [h, asymm h]

/-- A visit is determined by its crossing together with whether it is the later of the two
visits to that crossing. -/
theorem visit_isSecondVisit_injective :
    Function.Injective fun v : Fin (2 * n) => (D.visit v, D.isSecondVisit v) := by
  intro v w h
  simp only [Prod.mk.injEq] at h
  rcases (D.visit_eq_iff v w).mp h.1 with rfl | rfl
  · rfl
  · rw [isSecondVisit_partner] at h
    exact absurd h.2.symm (Bool.not_ne_self _)

/-- The visits of the traversal, indexed by the crossing visited together with whether the visit
is the later of the two to that crossing. -/
noncomputable def visitEquiv : Fin (2 * n) ≃ Fin n × Bool :=
  Equiv.ofBijective (fun v => (D.visit v, D.isSecondVisit v))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨D.visit_isSecondVisit_injective, by
        simp [Fintype.card_prod, Nat.mul_comm]⟩)

/-- The index of a visit is its crossing together with its position in the pair. -/
@[simp] theorem visitEquiv_apply (v : Fin (2 * n)) :
    D.visitEquiv v = (D.visit v, D.isSecondVisit v) := by
  simp [visitEquiv]

/-- The visit to crossing `i` that is the first (`second = false`) or the second
(`second = true`) of the two along the traversal. -/
noncomputable def visitAt (i : Fin n) (second : Bool) : Fin (2 * n) :=
  D.visitEquiv.symm (i, second)

/-- The visit at a crossing and index is a visit to that crossing with that index. -/
theorem visitEquiv_visitAt (i : Fin n) (s : Bool) :
    D.visitEquiv (D.visitAt i s) = (i, s) :=
  D.visitEquiv.apply_symm_apply (i, s)

/-- The visit selected at a crossing is a visit to that crossing. -/
@[simp] theorem visit_visitAt (i : Fin n) (s : Bool) : D.visit (D.visitAt i s) = i := by
  have h := D.visitEquiv_visitAt i s
  rw [visitEquiv_apply] at h
  exact congrArg Prod.fst h

/-- The visit selected at a crossing has the requested position in the pair. -/
@[simp] theorem isSecondVisit_visitAt (i : Fin n) (s : Bool) :
    D.isSecondVisit (D.visitAt i s) = s := by
  have h := D.visitEquiv_visitAt i s
  rw [visitEquiv_apply] at h
  exact congrArg Prod.snd h

/-- Selecting the visit at a visit's own crossing and position recovers it. -/
@[simp] theorem visitAt_visit (v : Fin (2 * n)) :
    D.visitAt (D.visit v) (D.isSecondVisit v) = v := by
  have h := D.visitEquiv.symm_apply_apply v
  rwa [visitEquiv_apply] at h

/-- The two visits to a crossing are partners in the matching. -/
theorem partner_visitAt (i : Fin n) (s : Bool) :
    D.partner.val (D.visitAt i s) = D.visitAt i (!s) := by
  have h := D.visitAt_visit (D.partner.val (D.visitAt i s))
  rw [visit_partner, visit_visitAt, isSecondVisit_partner, isSecondVisit_visitAt] at h
  exact h.symm

/-- The two visits to a crossing carry opposite over/under data. -/
theorem over_visitAt_not (i : Fin n) (s : Bool) :
    D.over (D.visitAt i (!s)) = !D.over (D.visitAt i s) := by
  rw [← partner_visitAt, over_partner]

/-- The direction to give to slot `1` of a crossing: it agrees with the over/under datum of the
second visit exactly when the crossing is positive. This is the choice that makes the sign
derived from the PD-code equal the sign recorded by the Gauss code. -/
noncomputable def slotOneDirection (i : Fin n) : Bool :=
  if D.sign i = 1 then D.over (D.visitAt i true) else !D.over (D.visitAt i true)

/-- The direction of slot `1` agrees with the over/under datum of the second visit exactly at a
positive crossing. -/
theorem slotOneDirection_eq_over_iff (i : Fin n) :
    D.slotOneDirection i = D.over (D.visitAt i true) ↔ D.sign i = 1 := by
  unfold slotOneDirection
  split <;> simp_all

/-- The half-edge in slot `s` of crossing `i`, as a visit together with a direction. -/
noncomputable def slotEquiv : Fin n × Fin 4 ≃ Fin (2 * n) × Bool :=
  (Equiv.sigmaEquivProd (Fin n) (Fin 4)).symm.trans
    (((Equiv.sigmaCongrRight fun i => PDCode.slotSplit (D.slotOneDirection i)).trans
        (Equiv.sigmaEquivProd (Fin n) (Bool × Bool))).trans
      ((Equiv.prodAssoc (Fin n) Bool Bool).symm.trans
        (D.visitEquiv.symm.prodCongr (Equiv.refl Bool))))

/-- The half-edge in a slot is read off the visit and direction that slot records. -/
@[simp] theorem slotEquiv_apply (i : Fin n) (s : Fin 4) :
    D.slotEquiv (i, s) =
      (D.visitAt i (PDCode.slotSplit (D.slotOneDirection i) s).1,
        (PDCode.slotSplit (D.slotOneDirection i) s).2) := (rfl)

/-- The oriented PD-code of a based oriented Gauss code.

Slots `0` and `2` at a crossing are the strand of its first visit and slots `1` and `3` the
strand of its second, so `overPair` is the over/under datum at the second visit; the direction
of slot `1` encodes the crossing sign. A code with no crossings is the single crossing-free
circle the traversal walks, recorded with the reference orientation. -/
noncomputable def toOrientedPDCode : OrientedPDCode n where
  halfEdge := (PDCode.crossingSlotEquiv n).symm.trans (D.slotEquiv.trans (PDCode.halfEdgeEquiv n))
  edgePair := PerfectMatching.congr (PDCode.halfEdgeEquiv n) (PDCode.visitArcMatching (2 * n))
  crossinglessComponentCount := if n = 0 then 1 else 0
  overPair i := D.over (D.visitAt i true)
  orientation h := ((PDCode.halfEdgeEquiv n).symm h).2
  orientation_edgePair := by
    intro h
    rw [PerfectMatching.congr_val_apply, Equiv.symm_apply_apply, PDCode.visitArcMatching_val,
      PDCode.visitArcMap_snd]
  orientation_oppositeCrossingSlot := by
    intro i slot
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, slotEquiv_apply,
      PDCode.slotSplit_snd_oppositeCrossingSlot]
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
@[simp] theorem toOrientedPDCode_halfEdge (i : Fin n) (s : Fin 4) :
    D.toOrientedPDCode.halfEdge (PDCode.crossingSlotEquiv n (i, s)) =
      PDCode.halfEdgeEquiv n (D.slotEquiv (i, s)) := by
  simp [toOrientedPDCode]

/-- The half-edge in slot `s` of crossing `i` is the one at the visit that slot belongs to,
carrying the direction that slot records. -/
theorem toOrientedPDCode_crossing (i : Fin n) (s : Fin 4) :
    D.toOrientedPDCode.crossing i s =
      PDCode.halfEdgeEquiv n
        (D.visitAt i (PDCode.slotSplit (D.slotOneDirection i) s).1,
          (PDCode.slotSplit (D.slotOneDirection i) s).2) := by
  rw [OrientedPDCode.crossing_apply, toOrientedPDCode_halfEdge, slotEquiv_apply]

/-- The arcs of the diagram join the half-edge leaving a visit to the half-edge entering the
next visit along the traversal. -/
theorem toOrientedPDCode_edgePair (v : Fin (2 * n)) :
    D.toOrientedPDCode.edgePair.val (PDCode.halfEdgeEquiv n (v, true)) =
      PDCode.halfEdgeEquiv n (finRotate (2 * n) v, false) := by
  have h : D.toOrientedPDCode.edgePair =
      PerfectMatching.congr (PDCode.halfEdgeEquiv n) (PDCode.visitArcMatching (2 * n)) := (rfl)
  rw [h, PerfectMatching.congr_val_apply_apply, PDCode.visitArcMatching_val]
  rfl

/-- The direction of the half-edge in a slot is the one that slot records. -/
theorem toOrientedPDCode_orientation_crossing (i : Fin n) (s : Fin 4) :
    D.toOrientedPDCode.orientation (D.toOrientedPDCode.crossing i s) =
      (PDCode.slotSplit (D.slotOneDirection i) s).2 := by
  simp [toOrientedPDCode]

/-- The over strand of a crossing of the PD-code is the strand of the visit the Gauss code
records as over. -/
theorem isOver_toOrientedPDCode_one (i : Fin n) :
    D.toOrientedPDCode.toPDCode.isOver i 1 = D.over (D.visitAt i true) := by
  simp

/-- The under strand of a crossing of the PD-code is the strand of the visit the Gauss code
records as under. -/
theorem isOver_toOrientedPDCode_zero (i : Fin n) :
    D.toOrientedPDCode.toPDCode.isOver i 0 = D.over (D.visitAt i false) := by
  have h := D.over_visitAt_not i true
  simp only [Bool.not_true] at h
  rw [PDCode.isOver_zero, toOrientedPDCode_overPair, h]

/-- **The signs agree**: the sign the PD-code derives from its slot order at a crossing is the
sign the Gauss code records there. -/
@[simp] theorem crossingSign_toOrientedPDCode (i : Fin n) :
    D.toOrientedPDCode.crossingSign i = (D.sign i : ℤ) := by
  have hpos : D.toOrientedPDCode.crossingSign i = 1 ↔ D.sign i = 1 := by
    rw [OrientedPDCode.crossingSign_eq_one_iff]
    simp only [toOrientedPDCode_orientation_crossing, PDCode.slotSplit_zero, PDCode.slotSplit_one,
      Bool.false_xor, toOrientedPDCode_overPair]
    exact D.slotOneDirection_eq_over_iff i
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
@[simp] theorem writhe_toOrientedPDCode : D.toOrientedPDCode.writhe = D.writhe := by
  simp [OrientedPDCode.writhe_def, writhe_def]

/-- The map to oriented PD-codes is injective: the crossing-incidence data remembers the whole
traversal. -/
theorem toOrientedPDCode_injective :
    Function.Injective (toOrientedPDCode (n := n)) := by
  intro D E h
  have hslot : ∀ (i : Fin n) (s : Fin 4), D.slotEquiv (i, s) = E.slotEquiv (i, s) := by
    intro i s
    refine (PDCode.halfEdgeEquiv n).injective ?_
    have := congrArg (fun C => C.halfEdge (PDCode.crossingSlotEquiv n (i, s))) h
    simpa using this
  have hvisitAt : ∀ (i : Fin n) (s : Bool), D.visitAt i s = E.visitAt i s := by
    intro i s
    cases s
    · simpa using congrArg Prod.fst (hslot i 0)
    · simpa using congrArg Prod.fst (hslot i 1)
  have hdir : ∀ i : Fin n, D.slotOneDirection i = E.slotOneDirection i := by
    intro i
    simpa using congrArg Prod.snd (hslot i 1)
  have hequiv : D.visitEquiv = E.visitEquiv := by
    have : D.visitEquiv.symm = E.visitEquiv.symm :=
      Equiv.ext fun p => hvisitAt p.1 p.2
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

end FramedBasedOrientedGaussCode

end TauCeti
