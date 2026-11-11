/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.Kink
public import TauCeti.KnotTheory.GaussCode.PDCode.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
import TauCeti.Data.Fin.Basic

/-!
# Kinks in Gauss codes are first Reidemeister moves

A *kink* is a small loop of a knot diagram crossing itself once. Read along the traversal of the
knot, it is a crossing whose two visits come one right after the other, and the first
Reidemeister move adds or removes one. This file shows that inserting a kink into a based oriented
Gauss code changes the PD-code of the diagram (`TauCeti.BasedOrientedGaussCode.toOrientedPDCode`)
only up to Reidemeister equivalence.

`TauCeti.BasedOrientedGaussCode.insertKink D k o s`, from `TauCeti.KnotTheory.GaussCode.Kink`,
inserts two visits of a new crossing, the last one, at positions `k` and `k + 1` of the traversal
of `D`: the first of them is over exactly when `o` is true, and the new crossing has sign `s`.
This file first reads the crossing slots and directions of the new code off those of `D`.

**Kinks are first Reidemeister moves**
(`TauCeti.BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_insertKink`): the PD-codes of
`D` and of `D.insertKink k o s` are Reidemeister equivalent. When `D` has crossings, the kink with
its loop on one side of the cut arc is the kink that `TauCeti.OrientedPDCode.reidemeisterOne`
inserts at the outgoing end of the visit before it, and the kink on the other side is the one it
inserts at the incoming end of the visit after it. In both cases the two crossing types differ in
the over-pair indicator of the new crossing, and the slots are matched with the conventions of
`toOrientedPDCode` by reading the new crossing from another slot
(`TauCeti.OrientedPDCode.rotateCrossing`). When `D` has no crossing, its PD-code is a crossing-free
circle and the kink is `TauCeti.OrientedPDCode.adjoinKink`. In each case the comparison of the
codes is `TauCeti.BasedOrientedGaussCode.relabel_toOrientedPDCode_eq`: a PD-code whose arcs,
directions and crossings are read off the traversal of a Gauss code is a relabelling of the
PD-code of that Gauss code.

This is how a first Reidemeister move shows up in a Gauss code, for instance in one read off a
regular projection of a polygonal knot (`Polygon.gaussCode`).

## Main results

* `TauCeti.BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_insertKink`: inserting a
  kink does not change the PD-code up to Reidemeister equivalence.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 (knot
  diagrams and the Reidemeister moves).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2--3 (the PD convention).
-/

public section

namespace TauCeti

namespace BasedOrientedGaussCode

variable {n : ℕ}

/-! ### Crossing slots of a code with a kink -/

variable (D : BasedOrientedGaussCode n) (k : Fin (2 * n + 1)) (o : Bool) (s : ℤˣ)

/-- An old crossing is read off the slots of the code with a kink as before. -/
@[simp]
theorem crossingVisit_insertKink_castSucc (c : Fin n) (slot : Fin 4) :
    (D.insertKink k o s).crossingVisit c.castSucc slot =
      kinkVisitEquiv n k (.inl (D.crossingVisit c slot)) := by
  apply (D.insertKink k o s).visitDataEquiv.injective
  simp [visitDataEquiv_apply]

/-- Slots `0` and `2` of the new crossing hold its over visit, which is the first inserted visit
exactly when `o` is true; slots `1` and `3` hold its under visit. -/
@[simp]
theorem crossingVisit_insertKink_last (slot : Fin 4) :
    (D.insertKink k o s).crossingVisit (Fin.last n) slot =
      kinkVisitEquiv n k (.inr (if decide (slot = 0 ∨ slot = 2) = o then 0 else 1)) := by
  apply (D.insertKink k o s).visitDataEquiv.injective
  simp only [visitDataEquiv_apply, visit_crossingVisit, over_crossingVisit, visit_insertKink_inr,
    Prod.mk.injEq, true_and]
  split_ifs with h
  · rw [over_insertKink_inr_zero, h]
  · rw [over_insertKink_inr_one]
    cases o
    · simp_all only [Bool.not_false]
    · simp_all

/-- The directions at the slots of an old crossing are unchanged. -/
@[simp]
theorem crossingOutgoing_insertKink_castSucc (c : Fin n) (slot : Fin 4) :
    (D.insertKink k o s).crossingOutgoing c.castSucc slot = D.crossingOutgoing c slot := by
  simp [crossingOutgoing_def]

/-- The directions at the slots of the new crossing are those of a crossing of sign `s`. -/
@[simp]
theorem crossingOutgoing_insertKink_last (slot : Fin 4) :
    (D.insertKink k o s).crossingOutgoing (Fin.last n) slot =
      if s = 1 then decide (slot = 2 ∨ slot = 3) else decide (slot = 1 ∨ slot = 2) := by
  rw [crossingOutgoing_def, sign_insertKink_last]

/-! ### The PD-code of a code with a kink -/

/-- The slots of the kink taken by the incoming and outgoing ends of the two inserted visits. For
`side = false` the kink is the one `TauCeti.OrientedPDCode.reidemeisterOne` cuts into the arc at
the outgoing end of the visit before it, entered at slot `0`; for `side = true` it is the one cut
into the same arc at the incoming end of the visit after it, entered at slot `1`. -/
private def kinkSlot (side : Bool) (p : Fin 2 × Bool) : Fin 4 :=
  if side then (if p.1 = 0 then (if p.2 then 3 else 1) else (if p.2 then 0 else 2))
  else (if p.1 = 0 then (if p.2 then 2 else 0) else (if p.2 then 1 else 3))

private theorem kinkSlot_bijective (side : Bool) : Function.Bijective (kinkSlot side) := by
  cases side <;> decide

private noncomputable def kinkSlotEquiv (side : Bool) : Fin 2 × Bool ≃ Fin 4 :=
  Equiv.ofBijective _ (kinkSlot_bijective side)

private theorem kinkSlotEquiv_apply (side : Bool) (p : Fin 2 × Bool) :
    kinkSlotEquiv side p = kinkSlot side p :=
  (rfl)

/-- The half-edges of the PD-code with one crossing more, labelled by the ends of the visits of the
code with a kink: an end of an old visit by the same end in the old code, an end of an inserted
visit by a slot of the new crossing, as prescribed by `τ`. -/
private noncomputable def kinkHalfEdgeEquiv (k : Fin (2 * n + 1)) (τ : Fin 2 × Bool ≃ Fin 4) :
    Fin (2 * (n + 1)) × Bool ≃ Fin (4 * (n + 1)) :=
  (Equiv.prodCongr (kinkVisitEquiv n k).symm (Equiv.refl Bool)).trans <|
    (Equiv.sumProdDistrib _ _ _).trans <|
      (Equiv.sumCongr (visitHalfEdgeEquiv n) τ).trans (PDCode.halfEdgeSuccEquiv n)

private theorem kinkHalfEdgeEquiv_inl (τ : Fin 2 × Bool ≃ Fin 4) (j : Fin (2 * n)) (b : Bool) :
    kinkHalfEdgeEquiv k τ (kinkVisitEquiv n k (.inl j), b) =
      PDCode.halfEdgeSuccEquiv n (.inl (visitHalfEdgeEquiv n (j, b))) := by
  simp [kinkHalfEdgeEquiv]

private theorem kinkHalfEdgeEquiv_inr (τ : Fin 2 × Bool ≃ Fin 4) (t : Fin 2) (b : Bool) :
    kinkHalfEdgeEquiv k τ (kinkVisitEquiv n k (.inr t), b) =
      PDCode.halfEdgeSuccEquiv n (.inr (τ (t, b))) := by
  simp [kinkHalfEdgeEquiv]

/-- Read the last crossing of a code `r` times from its next slot. -/
private def rotateLast (r : ℕ) (C : OrientedPDCode (n + 1)) : OrientedPDCode (n + 1) :=
  (fun C ↦ C.rotateCrossing (Fin.last n))^[r] C

private theorem rotateLast_succ (r : ℕ) (C : OrientedPDCode (n + 1)) :
    rotateLast (r + 1) C = (rotateLast r C).rotateCrossing (Fin.last n) :=
  Function.iterate_succ_apply' _ _ _

private theorem rotateLast_zero (C : OrientedPDCode (n + 1)) : rotateLast 0 C = C :=
  Function.iterate_zero_apply _ _

private theorem rotateLast_edgePair (r : ℕ) (C : OrientedPDCode (n + 1)) :
    (rotateLast r C).edgePair = C.edgePair := by
  induction r with
  | zero => rw [rotateLast_zero]
  | succ r ih => simp [rotateLast_succ, ih]

private theorem rotateLast_orientation (r : ℕ) (C : OrientedPDCode (n + 1)) :
    (rotateLast r C).orientation = C.orientation := by
  induction r with
  | zero => rw [rotateLast_zero]
  | succ r ih => simp [rotateLast_succ, ih]

private theorem rotateLast_crossinglessComponentCount (r : ℕ) (C : OrientedPDCode (n + 1)) :
    (rotateLast r C).crossinglessComponentCount = C.crossinglessComponentCount := by
  induction r with
  | zero => rw [rotateLast_zero]
  | succ r ih => simp [rotateLast_succ, ih]

private theorem rotateLast_halfEdge_castSucc (r : ℕ) (C : OrientedPDCode (n + 1)) (c : Fin n)
    (slot : Fin 4) :
    (rotateLast r C).halfEdge (PDCode.crossingSlotEquiv (n + 1) (c.castSucc, slot)) =
      C.halfEdge (PDCode.crossingSlotEquiv (n + 1) (c.castSucc, slot)) := by
  induction r with
  | zero => rw [rotateLast_zero]
  | succ r ih =>
    rw [rotateLast_succ, OrientedPDCode.toPDCode_rotateCrossing,
      PDCode.rotateCrossing_crossing_of_ne _ _ (Fin.castSucc_ne_last c), ih]

private theorem rotateLast_halfEdge_last (r : ℕ) (C : OrientedPDCode (n + 1)) (slot : Fin 4) :
    (rotateLast r C).halfEdge (PDCode.crossingSlotEquiv (n + 1) (Fin.last n, slot)) =
      C.halfEdge (PDCode.crossingSlotEquiv (n + 1) (Fin.last n, slot + Fin.ofNat 4 r)) := by
  induction r generalizing slot with
  | zero => simp [rotateLast_zero]
  | succ r ih =>
    rw [rotateLast_succ, OrientedPDCode.toPDCode_rotateCrossing,
      PDCode.rotateCrossing_crossing_self, ih]
    congr 3
    ext
    simp only [Fin.val_add, Fin.val_ofNat, Fin.val_one]
    omega

private theorem rotateLast_overPair_castSucc (r : ℕ) (C : OrientedPDCode (n + 1)) (c : Fin n) :
    (rotateLast r C).overPair c.castSucc = C.overPair c.castSucc := by
  induction r with
  | zero => rw [rotateLast_zero]
  | succ r ih =>
    rw [rotateLast_succ, OrientedPDCode.toPDCode_rotateCrossing,
      PDCode.rotateCrossing_overPair_of_ne _ _ (Fin.castSucc_ne_last c), ih]

private theorem rotateLast_overPair_last (r : ℕ) (C : OrientedPDCode (n + 1)) :
    (rotateLast r C).overPair (Fin.last n) = (C.overPair (Fin.last n) ^^ decide (r % 2 = 1)) := by
  induction r with
  | zero => simp [rotateLast_zero]
  | succ r ih =>
    rw [rotateLast_succ, OrientedPDCode.toPDCode_rotateCrossing,
      PDCode.rotateCrossing_overPair_self, ih]
    rcases Nat.mod_two_eq_zero_or_one r with h | h <;>
      simp [h, Nat.succ_mod_two_eq_one_iff]

private theorem reidemeisterEquiv_rotateLast (r : ℕ) (C : OrientedPDCode (n + 1)) :
    OrientedPDCode.ReidemeisterEquiv C (rotateLast r C) := by
  induction r with
  | zero => rw [rotateLast_zero]
  | succ r ih =>
    rw [rotateLast_succ]
    exact ih.trans (OrientedPDCode.reidemeisterEquiv_rotateCrossing _ _)

/-! ### A kink cut into an arc -/

section Arc

variable (D : BasedOrientedGaussCode (n + 1)) (k : Fin (2 * (n + 1) + 1)) (o : Bool) (s : ℤˣ)

/-- The old visit just before the inserted kink, cyclically. -/
private def kinkPrev (k : Fin (2 * (n + 1) + 1)) : Fin (2 * (n + 1)) :=
  ⟨if k.val = 0 then 2 * n + 1 else k.val - 1, by split_ifs <;> omega⟩

private theorem kinkPrev_val (k : Fin (2 * (n + 1) + 1)) :
    (kinkPrev k).val = if k.val = 0 then 2 * n + 1 else k.val - 1 :=
  (rfl)

private theorem finRotate_kinkVisitEquiv_inl {j : Fin (2 * (n + 1))} (hj : j ≠ kinkPrev k) :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inl j)) =
      kinkVisitEquiv (n + 1) k (.inl (finRotate _ j)) := by
  rw [Ne, Fin.ext_iff] at hj
  ext
  simp only [Fin.coe_finRotate_eq_ite, kinkVisitEquiv_apply_inl_val, kinkPrev_val] at hj ⊢
  split_ifs at hj ⊢ <;> omega

private theorem finRotate_kinkVisitEquiv_kinkPrev :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inl (kinkPrev k))) =
      kinkVisitEquiv (n + 1) k (.inr 0) := by
  ext
  simp only [Fin.coe_finRotate_eq_ite, kinkVisitEquiv_apply_inl_val, kinkVisitEquiv_apply_inr_val,
    kinkPrev_val, Fin.val_zero]
  split_ifs <;> omega

private theorem finRotate_kinkVisitEquiv_inr_zero :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inr 0)) = kinkVisitEquiv (n + 1) k (.inr 1) := by
  ext
  simp only [Fin.coe_finRotate_eq_ite, kinkVisitEquiv_apply_inr_val, Fin.val_zero, Fin.val_one]
  split_ifs <;> omega

private theorem finRotate_kinkVisitEquiv_inr_one :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inr 1)) =
      kinkVisitEquiv (n + 1) k (.inl (finRotate _ (kinkPrev k))) := by
  ext
  simp only [Fin.coe_finRotate_eq_ite, kinkVisitEquiv_apply_inl_val, kinkVisitEquiv_apply_inr_val,
    kinkPrev_val, Fin.val_one]
  split_ifs <;> omega

/-- The end of the cut arc at which `TauCeti.OrientedPDCode.reidemeisterOne` inserts the kink: the
outgoing end of the visit before it for `side = false`, and the incoming end of the visit after it
for `side = true`. -/
private def kinkArcEnd (k : Fin (2 * (n + 1) + 1)) (side : Bool) : Fin (4 * (n + 1)) :=
  if side then visitHalfEdgeEquiv (n + 1) (finRotate _ (kinkPrev k), false)
  else visitHalfEdgeEquiv (n + 1) (kinkPrev k, true)

private theorem kinkArcEnd_false :
    kinkArcEnd k false = visitHalfEdgeEquiv (n + 1) (kinkPrev k, true) :=
  (rfl)

private theorem kinkArcEnd_true :
    kinkArcEnd k true = visitHalfEdgeEquiv (n + 1) (finRotate _ (kinkPrev k), false) :=
  (rfl)

/-- The two choices of end are the two ends of the cut arc. -/
private theorem edgePair_kinkArcEnd_true :
    D.toOrientedPDCode.edgePair.val (kinkArcEnd k true) = kinkArcEnd k false := by
  simp [kinkArcEnd]

private theorem orientation_kinkArcEnd (side : Bool) :
    D.toOrientedPDCode.orientation (kinkArcEnd k side) = !side := by
  cases side <;> simp [kinkArcEnd]

/-- The arcs of the code with the kink cut in follow the traversal of the Gauss code with the
kink, through the labelling `kinkHalfEdgeEquiv`. -/
private theorem edgePair_reidemeisterOne_kinkHalfEdgeEquiv (side b : Bool)
    (i : Fin (2 * (n + 1 + 1))) :
    (D.toOrientedPDCode.reidemeisterOne (kinkArcEnd k side) b).edgePair.val
        (kinkHalfEdgeEquiv k (kinkSlotEquiv side) (i, true)) =
      kinkHalfEdgeEquiv k (kinkSlotEquiv side) (finRotate _ i, false) := by
  obtain ⟨j | t, rfl⟩ := (kinkVisitEquiv (n + 1) k).surjective i
  · by_cases hj : j = kinkPrev k
    · -- The arc leaving the visit before the kink now enters the kink.
      subst hj
      rw [finRotate_kinkVisitEquiv_kinkPrev, kinkHalfEdgeEquiv_inl, kinkHalfEdgeEquiv_inr]
      cases side
      · simp [kinkArcEnd_false, kinkSlotEquiv_apply, kinkSlot]
      · rw [← kinkArcEnd_false, ← edgePair_kinkArcEnd_true D]
        simp [kinkSlotEquiv_apply, kinkSlot]
    · -- The other old arcs are unchanged.
      have hne (side' : Bool) : visitHalfEdgeEquiv (n + 1) (j, true) ≠ kinkArcEnd k side' := by
        cases side' <;> simp [kinkArcEnd, hj]
      rw [finRotate_kinkVisitEquiv_inl k hj, kinkHalfEdgeEquiv_inl, kinkHalfEdgeEquiv_inl,
        OrientedPDCode.toPDCode_reidemeisterOne,
        PDCode.reidemeisterOne_edgePair_inl_of_ne _ _ _ (hne side) (by
          cases side
          · simp [kinkArcEnd]
          · rw [edgePair_kinkArcEnd_true]
            exact hne false)]
      simp
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · -- The loop of the kink, from the first inserted visit to the second.
      rw [finRotate_kinkVisitEquiv_inr_zero, kinkHalfEdgeEquiv_inr, kinkHalfEdgeEquiv_inr]
      cases side <;> simp [kinkSlotEquiv_apply, kinkSlot]
    · -- The arc leaving the kink enters the visit after it.
      rw [finRotate_kinkVisitEquiv_inr_one, kinkHalfEdgeEquiv_inr, kinkHalfEdgeEquiv_inl]
      cases side
      · simp [kinkSlotEquiv_apply, kinkSlot, kinkArcEnd]
      · simp [kinkSlotEquiv_apply, kinkSlot, kinkArcEnd_true]

/-- The directions in the code with the kink cut in are those read off the traversal of the Gauss
code with the kink. -/
private theorem orientation_reidemeisterOne_kinkHalfEdgeEquiv (side b : Bool)
    (i : Fin (2 * (n + 1 + 1))) (b' : Bool) :
    (D.toOrientedPDCode.reidemeisterOne (kinkArcEnd k side) b).orientation
        (kinkHalfEdgeEquiv k (kinkSlotEquiv side) (i, b')) = b' := by
  obtain ⟨j | t, rfl⟩ := (kinkVisitEquiv (n + 1) k).surjective i
  · rw [kinkHalfEdgeEquiv_inl, OrientedPDCode.orientation_reidemeisterOne_inl]
    simp
  · rw [kinkHalfEdgeEquiv_inr]
    fin_cases t <;> cases b' <;> cases side <;>
      simp [kinkSlotEquiv_apply, kinkSlot, orientation_kinkArcEnd]

/-- The PD-code of a Gauss code with a kink is a relabelling of the code obtained from the old one
by `TauCeti.OrientedPDCode.reidemeisterOne` at the end `kinkArcEnd k side` of the cut arc, with
over-pair indicator `b`, its new crossing then read `r` times from the next slot, as soon as these
choices put the ends of the two inserted visits in the slots that the conversion of Gauss codes
uses. -/
private theorem relabel_toOrientedPDCode_insertKink_eq (side b : Bool) (r : ℕ)
    (hslot : ∀ slot : Fin 4, kinkSlot side (if decide (slot = 0 ∨ slot = 2) = o then 0 else 1,
      if s = 1 then decide (slot = 2 ∨ slot = 3) else decide (slot = 1 ∨ slot = 2)) =
        slot + Fin.ofNat 4 r)
    (hb : (b ^^ decide (r % 2 = 1)) = false) :
    (D.insertKink k o s).toOrientedPDCode.relabel
        ((visitHalfEdgeEquiv (n + 1 + 1)).symm.trans (kinkHalfEdgeEquiv k (kinkSlotEquiv side)))
        (Equiv.refl _) =
      rotateLast r (D.toOrientedPDCode.reidemeisterOne (kinkArcEnd k side) b) := by
  apply relabel_toOrientedPDCode_eq (by omega)
  · intro i
    rw [rotateLast_edgePair]
    exact edgePair_reidemeisterOne_kinkHalfEdgeEquiv D k side b i
  · intro i b'
    rw [rotateLast_orientation]
    exact orientation_reidemeisterOne_kinkHalfEdgeEquiv D k side b i b'
  · intro c slot
    induction c using Fin.lastCases with
    | last =>
      rw [rotateLast_halfEdge_last, crossingVisit_insertKink_last, crossingOutgoing_insertKink_last,
        kinkHalfEdgeEquiv_inr, kinkSlotEquiv_apply, hslot,
        PDCode.crossingSlotEquiv_succ_last, OrientedPDCode.toPDCode_reidemeisterOne,
        PDCode.reidemeisterOne_crossing_last]
    | cast c =>
      rw [rotateLast_halfEdge_castSucc, crossingVisit_insertKink_castSucc,
        crossingOutgoing_insertKink_castSucc, kinkHalfEdgeEquiv_inl,
        PDCode.crossingSlotEquiv_succ_castSucc, OrientedPDCode.toPDCode_reidemeisterOne,
        PDCode.reidemeisterOne_crossing_castSucc, PDCode.crossing_apply, toOrientedPDCode_crossing]
  · intro c
    induction c using Fin.lastCases with
    | last => rw [rotateLast_overPair_last]; simpa using hb
    | cast c => rw [rotateLast_overPair_castSucc]; simp
  · rw [rotateLast_crossinglessComponentCount]
    simp

/-- Inserting a kink into a Gauss code with at least one crossing changes its PD-code by a first
Reidemeister move, followed by a rotation of the new crossing and a relabelling. -/
private theorem reidemeisterEquiv_toOrientedPDCode_insertKink_succ :
    OrientedPDCode.ReidemeisterEquiv D.toOrientedPDCode (D.insertKink k o s).toOrientedPDCode := by
  obtain ⟨side, b, r, hslot, hb⟩ : ∃ side b : Bool, ∃ r : ℕ,
      (∀ slot : Fin 4, kinkSlot side (if decide (slot = 0 ∨ slot = 2) = o then 0 else 1,
        if s = 1 then decide (slot = 2 ∨ slot = 3) else decide (slot = 1 ∨ slot = 2)) =
          slot + Fin.ofNat 4 r) ∧ (b ^^ decide (r % 2 = 1)) = false := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> cases o
    · exact ⟨false, true, 3, by decide, by decide⟩
    · exact ⟨true, true, 1, by decide, by decide⟩
    · exact ⟨true, false, 2, by decide, by decide⟩
    · exact ⟨false, false, 0, by decide, by decide⟩
  refine ((OrientedPDCode.reidemeisterEquiv_reidemeisterOne _ (kinkArcEnd k side) b).trans
    (reidemeisterEquiv_rotateLast r _)).trans ?_
  rw [← relabel_toOrientedPDCode_insertKink_eq D k o s side b r hslot hb]
  exact (OrientedPDCode.reidemeisterEquiv_relabel _ _ _).symm

end Arc

/-! ### A kink on a crossing-free circle -/

section Circle

variable (D : BasedOrientedGaussCode 0) (k : Fin (2 * 0 + 1)) (o : Bool) (s : ℤˣ)

private theorem finRotate_kinkVisitEquiv_zero (t : Fin 2) :
    finRotate _ (kinkVisitEquiv 0 k (.inr t)) = kinkVisitEquiv 0 k (.inr (t + 1)) := by
  have hk : k.val = 0 := by omega
  ext
  simp only [Fin.coe_finRotate_eq_ite, kinkVisitEquiv_apply_inr_val, hk]
  fin_cases t <;> simp

/-- The PD-code of the crossing-free Gauss code with a kink is a relabelling of the kink adjoined
to the crossing-free circle, its crossing read `r` times from the next slot, as soon as `τ` puts
the ends of the two visits into the slots of that kink and the conversion of Gauss codes puts
them where `τ` does. -/
private theorem relabel_toOrientedPDCode_insertKink_eq_zero (τ : Fin 2 × Bool → Fin 4)
    (hτ : Function.Bijective τ) (b : Bool) (r : ℕ)
    (hedge : ∀ t, PDCode.slotSmoothing true (τ (t, true)) = τ (t + 1, false))
    (horient : ∀ t b', ![false, true, true, false] (τ (t, b')) = b')
    (hslot : ∀ slot : Fin 4, τ (if decide (slot = 0 ∨ slot = 2) = o then 0 else 1,
      if s = 1 then decide (slot = 2 ∨ slot = 3) else decide (slot = 1 ∨ slot = 2)) =
        slot + Fin.ofNat 4 r)
    (hb : (b ^^ decide (r % 2 = 1)) = false) :
    (D.insertKink k o s).toOrientedPDCode.relabel
        ((visitHalfEdgeEquiv (0 + 1)).symm.trans (kinkHalfEdgeEquiv k (Equiv.ofBijective τ hτ)))
        (Equiv.refl _) =
      rotateLast r (OrientedPDCode.empty.adjoinKink true b) := by
  apply relabel_toOrientedPDCode_eq (by omega)
  · intro i
    obtain ⟨x | t, rfl⟩ := (kinkVisitEquiv 0 k).surjective i
    · exact x.elim0
    · rw [rotateLast_edgePair, finRotate_kinkVisitEquiv_zero, kinkHalfEdgeEquiv_inr,
        kinkHalfEdgeEquiv_inr, OrientedPDCode.toPDCode_adjoinKink, PDCode.adjoinKink_edgePair_inr,
        Equiv.ofBijective_apply, Equiv.ofBijective_apply, hedge]
  · intro i b'
    obtain ⟨x | t, rfl⟩ := (kinkVisitEquiv 0 k).surjective i
    · exact x.elim0
    · rw [rotateLast_orientation, kinkHalfEdgeEquiv_inr, OrientedPDCode.orientation_adjoinKink_inr,
        Equiv.ofBijective_apply]
      simpa using horient t b'
  · intro c slot
    obtain rfl : c = Fin.last 0 := Fin.ext (by omega)
    rw [rotateLast_halfEdge_last, crossingVisit_insertKink_last, crossingOutgoing_insertKink_last,
      kinkHalfEdgeEquiv_inr, Equiv.ofBijective_apply, hslot, PDCode.crossingSlotEquiv_succ_last,
      OrientedPDCode.toPDCode_adjoinKink, PDCode.adjoinKink_halfEdge]
    simp [Equiv.permCongr_apply]
  · intro c
    obtain rfl : c = Fin.last 0 := Fin.ext (by omega)
    rw [rotateLast_overPair_last, OrientedPDCode.toPDCode_adjoinKink, PDCode.adjoinKink_overPair,
      Fin.snoc_last, hb]
  · rw [rotateLast_crossinglessComponentCount, OrientedPDCode.toPDCode_adjoinKink,
      PDCode.adjoinKink_crossinglessComponentCount, ← OrientedPDCode.card_crossinglessComponents,
      OrientedPDCode.crossinglessComponents_empty, Multiset.card_zero]

private theorem reidemeisterEquiv_toOrientedPDCode_insertKink_zero :
    OrientedPDCode.ReidemeisterEquiv D.toOrientedPDCode (D.insertKink k o s).toOrientedPDCode := by
  obtain ⟨τ, hτ, b, r, hedge, horient, hslot, hb⟩ : ∃ τ : Fin 2 × Bool → Fin 4,
      ∃ hτ : Function.Bijective τ, ∃ b : Bool, ∃ r : ℕ,
      (∀ t, PDCode.slotSmoothing true (τ (t, true)) = τ (t + 1, false)) ∧
      (∀ t b', ![false, true, true, false] (τ (t, b')) = b') ∧
      (∀ slot : Fin 4, τ (if decide (slot = 0 ∨ slot = 2) = o then 0 else 1,
        if s = 1 then decide (slot = 2 ∨ slot = 3) else decide (slot = 1 ∨ slot = 2)) =
          slot + Fin.ofNat 4 r) ∧ (b ^^ decide (r % 2 = 1)) = false := by
    let τ' : Fin 2 × Bool → Fin 4 := fun p ↦ kinkSlot false (p.1 + 1, p.2)
    have hswap : Function.Bijective τ' := by decide
    have hedge (τ : Fin 2 × Bool → Fin 4)
        (h : ∀ t, ![1, 0, 3, 2] (τ (t, true)) = τ (t + 1, false)) (t : Fin 2) :
        PDCode.slotSmoothing true (τ (t, true)) = τ (t + 1, false) := by
      rw [← h t, PDCode.slotSmoothing_true]
      generalize τ (t, true) = x
      fin_cases x <;> simp [Equiv.swap_apply_def]
    rcases Int.units_eq_one_or s with rfl | rfl <;> cases o
    · exact ⟨kinkSlot false, kinkSlot_bijective false, true, 3, hedge _ (by decide), by decide,
        by decide, by decide⟩
    · exact ⟨τ', hswap, true, 3, hedge τ' (by decide), by decide, by decide, by decide⟩
    · exact ⟨τ', hswap, false, 0, hedge τ' (by decide), by decide, by decide, by decide⟩
    · exact ⟨kinkSlot false, kinkSlot_bijective false, false, 0, hedge _ (by decide), by decide,
        by decide, by decide⟩
  have hD : D.toOrientedPDCode = OrientedPDCode.empty.adjoinCircle true :=
    OrientedPDCode.unlinkEquiv.symm.injective (by simp [OrientedPDCode.unlinkEquiv_symm_apply])
  rw [hD]
  refine ((OrientedPDCode.reidemeisterEquiv_adjoinKink _ true b).trans
    (reidemeisterEquiv_rotateLast r _)).trans ?_
  rw [← relabel_toOrientedPDCode_insertKink_eq_zero D k o s τ hτ b r hedge horient hslot hb]
  exact (OrientedPDCode.reidemeisterEquiv_relabel _ _ _).symm

end Circle

/-! ### Kinks are first Reidemeister moves -/

/-- **Kinks are first Reidemeister moves.** Inserting a kink into a based oriented Gauss code,
with a crossing of either sign whose first visit is over or under, so on either side of the cut
arc, changes the PD-code of the diagram by a first Reidemeister move: the two PD-codes are
Reidemeister equivalent. For the crossing-free code the kink is added to the crossing-free circle
(`TauCeti.OrientedPDCode.adjoinKink`); otherwise it is cut into an arc
(`TauCeti.OrientedPDCode.reidemeisterOne`), in both cases up to reading the new crossing from
another slot and relabelling. -/
theorem reidemeisterEquiv_toOrientedPDCode_insertKink (D : BasedOrientedGaussCode n)
    (k : Fin (2 * n + 1)) (o : Bool) (s : ℤˣ) :
    OrientedPDCode.ReidemeisterEquiv D.toOrientedPDCode (D.insertKink k o s).toOrientedPDCode := by
  cases n with
  | zero => exact reidemeisterEquiv_toOrientedPDCode_insertKink_zero D k o s
  | succ n => exact reidemeisterEquiv_toOrientedPDCode_insertKink_succ D k o s

end BasedOrientedGaussCode

end TauCeti
