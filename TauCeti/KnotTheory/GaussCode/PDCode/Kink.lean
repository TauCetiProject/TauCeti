/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.PDCode.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence

/-!
# Kinks in Gauss codes are first Reidemeister moves

A *kink* is a small loop of a knot diagram crossing itself once. Read along the traversal of the
knot, it is a crossing whose two visits come one right after the other, and the first
Reidemeister move adds or removes one. This file inserts kinks into based oriented Gauss codes and
shows that this changes the PD-code of the diagram
(`TauCeti.BasedOrientedGaussCode.toOrientedPDCode`) only up to Reidemeister equivalence.

`TauCeti.BasedOrientedGaussCode.insertKink D k o s` inserts two visits of a new crossing, the last
one, at positions `k` and `k + 1` of the traversal of `D`: the first of them is over exactly when
`o` is true, and the new crossing has sign `s`. The old visits keep their order, crossings,
over/under data and signs; `TauCeti.BasedOrientedGaussCode.kinkVisitEquiv` records where they go.
The four choices of `o` and `s` are the four kinks: for a kink of given sign, whether the strand
first passes over or under decides on which side of the cut arc its loop lies.

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

## Main definitions

* `TauCeti.BasedOrientedGaussCode.kinkVisitEquiv`: the positions of the old and the inserted
  visits after inserting two visits at position `k`.
* `TauCeti.BasedOrientedGaussCode.insertKink`: insert a kink into a based oriented Gauss code.

## Main results

* `TauCeti.BasedOrientedGaussCode.writhe_insertKink`: the kink adds its sign to the writhe.
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

/-! ### Inserting two consecutive visits -/

/-- The position of an old visit, or of one of the two new visits, after two visits are inserted
at position `k`. -/
private def kinkVisitFun (n : ℕ) (k : Fin (2 * n + 1)) : Fin (2 * n) ⊕ Fin 2 → Fin (2 * (n + 1)) :=
  Sum.elim (fun j ↦ ⟨if j.val < k.val then j.val else j.val + 2, by split_ifs <;> omega⟩)
    (fun t ↦ ⟨k.val + t.val, by omega⟩)

private theorem kinkVisitFun_injective (n : ℕ) (k : Fin (2 * n + 1)) :
    Function.Injective (kinkVisitFun n k) := by
  rintro (j | t) (j' | t') h <;>
    simp only [kinkVisitFun, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>
    (try split_ifs at h) <;> omega

/-- The visits of a Gauss code with two visits inserted at position `k`: the `2 * n` old visits,
in their old order, and the two new visits, which become visits `k` and `k + 1`. An old visit `j`
keeps its position if `j < k` and moves up by two otherwise. -/
noncomputable def kinkVisitEquiv (n : ℕ) (k : Fin (2 * n + 1)) :
    Fin (2 * n) ⊕ Fin 2 ≃ Fin (2 * (n + 1)) :=
  Equiv.ofBijective (kinkVisitFun n k) <| (kinkVisitFun_injective n k).bijective_of_nat_card_le
    (by simp [Nat.card_eq_fintype_card]; omega)

/-- An old visit keeps its position if it comes before the inserted visits, and moves up by two
otherwise. -/
@[simp]
theorem kinkVisitEquiv_apply_inl_val (k : Fin (2 * n + 1)) (j : Fin (2 * n)) :
    (kinkVisitEquiv n k (.inl j)).val = if j.val < k.val then j.val else j.val + 2 :=
  (rfl)

/-- The two inserted visits are visits `k` and `k + 1`. -/
@[simp]
theorem kinkVisitEquiv_apply_inr_val (k : Fin (2 * n + 1)) (t : Fin 2) :
    (kinkVisitEquiv n k (.inr t)).val = k.val + t.val :=
  (rfl)

/-- The matching of visits of a code with a kink inserted, before the visits are renumbered: the
old matching on the old visits, and the two new visits matched with each other. -/
private def kinkPartner (D : BasedOrientedGaussCode n) : PerfectMatching (Fin (2 * n) ⊕ Fin 2) :=
  PerfectMatching.mk (Equiv.sumCongr D.partner.val (Equiv.swap 0 1))
    (by rintro (j | t) <;> simp)
    (by
      rintro (j | t)
      · simp [D.partner.apply_ne]
      · simp only [Equiv.sumCongr_apply, Sum.map_inr, ne_eq, Sum.inr.injEq]
        fin_cases t <;> decide)

/-- Insert a **kink** into a based oriented Gauss code: two consecutive visits `k` and `k + 1` of a
new crossing, the last one, `Fin.last n`, of sign `s`. The first of the two visits is over exactly
when `o` is true. The old visits keep their order, crossings, over/under data and signs.

In a diagram this cuts the arc running from visit `k - 1` to visit `k` of the old code, cyclically,
and splices in a small loop crossing itself once. Each of the four choices of `o` and `s` is the
kink on one side of the arc with one of the two crossing types. -/
noncomputable def insertKink (D : BasedOrientedGaussCode n) (k : Fin (2 * n + 1)) (o : Bool)
    (s : ℤˣ) : BasedOrientedGaussCode (n + 1) where
  visit i := Sum.elim (fun j ↦ (D.visit j).castSucc) (fun _ ↦ Fin.last n)
    ((kinkVisitEquiv n k).symm i)
  over i := Sum.elim D.over (fun t ↦ if t = 0 then o else !o) ((kinkVisitEquiv n k).symm i)
  sign := Fin.lastCases s D.sign
  partner := PerfectMatching.congr (kinkVisitEquiv n k) (kinkPartner D)
  visit_eq_iff i j := by
    obtain ⟨x, rfl⟩ := (kinkVisitEquiv n k).surjective i
    obtain ⟨y, rfl⟩ := (kinkVisitEquiv n k).surjective j
    rw [PerfectMatching.congr_val_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      (kinkVisitEquiv n k).injective.eq_iff, (kinkVisitEquiv n k).injective.eq_iff]
    rcases x with x | t <;> rcases y with y | t'
    · simp [kinkPartner, Fin.castSucc_inj, D.visit_eq_iff, eq_comm]
    · simp [kinkPartner, Fin.castSucc_ne_last]
    · simp [kinkPartner, (Fin.castSucc_ne_last _).symm]
    · simp only [kinkPartner, PerfectMatching.val_mk, Equiv.sumCongr_apply, Sum.map_inr,
        Sum.elim_inr, Sum.inr.injEq, true_iff]
      fin_cases t <;> fin_cases t' <;> decide
  over_partner i := by
    obtain ⟨x, rfl⟩ := (kinkVisitEquiv n k).surjective i
    rw [PerfectMatching.congr_val_apply_apply, Equiv.symm_apply_apply]
    rcases x with x | t
    · simp [kinkPartner]
    · simp only [kinkPartner, PerfectMatching.val_mk, Equiv.sumCongr_apply, Sum.map_inr,
        Sum.elim_inr]
      fin_cases t <;> simp

variable (D : BasedOrientedGaussCode n) (k : Fin (2 * n + 1)) (o : Bool) (s : ℤˣ)

/-- An old visit keeps its crossing. -/
@[simp]
theorem visit_insertKink_inl (j : Fin (2 * n)) :
    (D.insertKink k o s).visit (kinkVisitEquiv n k (.inl j)) = (D.visit j).castSucc := by
  simp [insertKink]

/-- The two inserted visits are visits of the new last crossing. -/
@[simp]
theorem visit_insertKink_inr (t : Fin 2) :
    (D.insertKink k o s).visit (kinkVisitEquiv n k (.inr t)) = Fin.last n := by
  simp [insertKink]

/-- An old visit keeps its over/under data. -/
@[simp]
theorem over_insertKink_inl (j : Fin (2 * n)) :
    (D.insertKink k o s).over (kinkVisitEquiv n k (.inl j)) = D.over j := by
  simp [insertKink]

/-- The first inserted visit is over exactly when `o` is true. -/
@[simp]
theorem over_insertKink_inr_zero :
    (D.insertKink k o s).over (kinkVisitEquiv n k (.inr 0)) = o := by
  simp [insertKink]

/-- The second inserted visit is over exactly when `o` is false. -/
@[simp]
theorem over_insertKink_inr_one :
    (D.insertKink k o s).over (kinkVisitEquiv n k (.inr 1)) = !o := by
  simp [insertKink]

/-- An old crossing keeps its sign. -/
@[simp]
theorem sign_insertKink_castSucc (c : Fin n) :
    (D.insertKink k o s).sign c.castSucc = D.sign c := by
  simp [insertKink]

/-- The new crossing has sign `s`. -/
@[simp]
theorem sign_insertKink_last : (D.insertKink k o s).sign (Fin.last n) = s := by
  simp [insertKink]

/-- The partner of an old visit is the old partner. -/
@[simp]
theorem partner_insertKink_inl (j : Fin (2 * n)) :
    (D.insertKink k o s).partner.val (kinkVisitEquiv n k (.inl j)) =
      kinkVisitEquiv n k (.inl (D.partner.val j)) := by
  simp [insertKink, kinkPartner]

/-- The two inserted visits are partners. -/
@[simp]
theorem partner_insertKink_inr (t : Fin 2) :
    (D.insertKink k o s).partner.val (kinkVisitEquiv n k (.inr t)) =
      kinkVisitEquiv n k (.inr (t + 1)) := by
  simp only [insertKink, kinkPartner, PerfectMatching.congr_val_apply_apply,
    PerfectMatching.val_mk, Equiv.sumCongr_apply, Sum.map_inr]
  congr 2
  fin_cases t <;> rfl

/-- The kink adds the sign of its crossing to the writhe. -/
@[simp]
theorem writhe_insertKink : (D.insertKink k o s).writhe = D.writhe + s := by
  simp [writhe_def, Fin.sum_univ_castSucc]

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

/-- The rotation of the visits, read on their positions. Mathlib's `coe_finRotate` is stated for
`Fin (m + 1)`; the visits of a code with `m + 1` crossings form `Fin (2 * (m + 1))`, which is the
same type up to unfolding the multiplication, so the lemma applies but is not found by `rw`. -/
private theorem finRotate_val (m : ℕ) (i : Fin (2 * (m + 1))) :
    (finRotate _ i).val = if i.val = 2 * m + 1 then 0 else i.val + 1 := by
  refine (coe_finRotate (n := 2 * m + 1) i).trans ?_
  simp [Fin.ext_iff]

private theorem finRotate_kinkVisitEquiv_inl {j : Fin (2 * (n + 1))} (hj : j ≠ kinkPrev k) :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inl j)) =
      kinkVisitEquiv (n + 1) k (.inl (finRotate _ j)) := by
  rw [Ne, Fin.ext_iff] at hj
  ext
  simp only [finRotate_val, kinkVisitEquiv_apply_inl_val, kinkPrev_val] at hj ⊢
  split_ifs at hj ⊢ <;> omega

private theorem finRotate_kinkVisitEquiv_kinkPrev :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inl (kinkPrev k))) =
      kinkVisitEquiv (n + 1) k (.inr 0) := by
  ext
  simp only [finRotate_val, kinkVisitEquiv_apply_inl_val, kinkVisitEquiv_apply_inr_val,
    kinkPrev_val, Fin.val_zero]
  split_ifs <;> omega

private theorem finRotate_kinkVisitEquiv_inr_zero :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inr 0)) = kinkVisitEquiv (n + 1) k (.inr 1) := by
  ext
  simp only [finRotate_val, kinkVisitEquiv_apply_inr_val, Fin.val_zero, Fin.val_one]
  split_ifs <;> omega

private theorem finRotate_kinkVisitEquiv_inr_one :
    finRotate _ (kinkVisitEquiv (n + 1) k (.inr 1)) =
      kinkVisitEquiv (n + 1) k (.inl (finRotate _ (kinkPrev k))) := by
  ext
  simp only [finRotate_val, kinkVisitEquiv_apply_inl_val, kinkVisitEquiv_apply_inr_val,
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
  simp only [finRotate_val, kinkVisitEquiv_apply_inr_val, hk]
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
