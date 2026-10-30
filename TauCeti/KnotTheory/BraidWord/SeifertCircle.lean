/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert

/-!
# Seifert circles of a closed braid

The closure of a braid word on `n` strands has exactly `n` Seifert circles, one running along each
strand position. All strands of a braid run upwards, so at every crossing the
orientation-respecting smoothing cuts the crossing horizontally: it joins the strand entering from
below on a position to the strand leaving above on the same position. The Seifert circles of the
closure are therefore the `n` strand positions, each closed up through the closure. So a link
presented as the closure of an `n`-strand braid has a diagram with `n` Seifert circles, which is the
easy inequality in Yamada's theorem that the braid index of a link is the least number of Seifert
circles of its diagrams; and a closed braid is the configuration that Vogel's algorithm reaches
when it turns a diagram into a closed braid by moves on its Seifert circles.

In the closure `TauCeti.BraidWord.closure`, a strand leaving a crossing upwards on the position `p`
next enters the crossing `TauCeti.BraidWord.nextCrossing p` from below, and the Seifert smoothing
joins it there to the strand leaving that crossing upwards on `p` again. So the traversal of the
Seifert smoothing follows each strand position upwards through its crossings
(`TauCeti.BraidWord.statePerm_seifertState_closure_outgoingSlot`), and visits all of them. A
position involved in no crossing is a crossing-free component of the closure.

## Main definitions

* `TauCeti.BraidWord.seifertCircleEquiv`: the Seifert circles of the closure of a braid word are
  its strand positions.

## Main results

* `TauCeti.BraidWord.smoothingChoice_seifertState_closure`: the Seifert state of a closed braid
  selects the horizontal smoothing at every crossing.
* `TauCeti.BraidWord.statePerm_seifertState_closure_outgoingSlot`: its traversal follows each
  strand position upwards.
* `TauCeti.BraidWord.card_seifertCircle_closure`: the closure of a braid word on `n` strands has
  `n` Seifert circles.

## References

* S. Yamada, *The minimal number of Seifert circles equals the braid index of a link*, Invent.
  Math. 89 (1987), 347-356.
* P. Vogel, *Representation of links by braids: a new algorithm*, Comment. Math. Helv. 65 (1990),
  104-113.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (closed braids).
-/

public section

namespace TauCeti

namespace BraidWord

open BraidGroup Equiv Equiv.Perm PDCode OrientedPDCode

variable {n : ℕ} (w : BraidWord n)

/-! ### The Seifert smoothing of a closed braid -/

/-- **The Seifert smoothing of a closed braid is horizontal.** At every crossing of the closure the
Seifert state selects the smoothing joining the slots `0` and `1`, both on the upper position of
the letter, and the slots `2` and `3`, both on its lower position. -/
theorem smoothingChoice_seifertState_closure (j : Fin w.length) :
    w.closure.smoothingChoice w.closure.seifertState j = true := by
  rw [smoothingChoice_seifertState, crossing_closure, crossing_closure, orientation_closure,
    orientation_closure]
  decide

/-- The horizontal smoothing joins the slot at which a strand enters a crossing from below to the
slot at which it leaves upwards on the same position. -/
private theorem slotSmoothing_true_incomingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) :
    slotSmoothing true (w.incomingSlot j p) = w.outgoingSlot j p := by
  rcases w.mem_crossingsAt.1 hj with rfl | rfl <;>
    simp only [incomingSlot_strand, outgoingSlot_strand, incomingSlot_strandSucc,
      outgoingSlot_strandSucc, slotSmoothing_true] <;> decide

/-- **The traversal of the Seifert smoothing follows the strand positions upwards**: from the
strand leaving a crossing upwards on the position `p`, it leads to the strand leaving the next
crossing along `p` upwards. -/
theorem statePerm_seifertState_closure_outgoingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) :
    w.closure.statePerm w.closure.seifertState (w.closure.crossing j (w.outgoingSlot j p)) =
      w.closure.crossing (w.nextCrossing p j) (w.outgoingSlot (w.nextCrossing p j) p) := by
  rw [statePerm_apply, w.edgePair_closure_outgoingSlot hj, crossing_apply, smoothingTurn_crossing,
    smoothingChoice_seifertState_closure,
    w.slotSmoothing_true_incomingSlot (w.nextCrossing_mem_crossingsAt_iff.2 hj)]

/-- Iterating the traversal of the Seifert smoothing `k` times moves `k` crossings up along the
strand position. -/
private theorem pow_statePerm_seifertState_closure_outgoingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) (k : ℕ) :
    (w.closure.statePerm w.closure.seifertState ^ k)
        (w.closure.crossing j (w.outgoingSlot j p)) =
      w.closure.crossing ((w.nextCrossing p ^ k) j)
        (w.outgoingSlot ((w.nextCrossing p ^ k) j) p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih,
      w.statePerm_seifertState_closure_outgoingSlot (w.pow_nextCrossing_mem_crossingsAt hj k),
      pow_succ', Perm.mul_apply]

/-! ### The Seifert circles along the strand positions -/

/-- All crossings along a strand position lie on one Seifert circle: the circle through the
strand leaving any of them upwards is the circle through the strand leaving the lowest one. -/
theorem seifertCircle_mk_closure_outgoingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) :
    (⟦w.closure.crossing j (w.outgoingSlot j p)⟧ :
        w.closure.CrossingCircle w.closure.seifertState) =
      ⟦w.closure.crossing ((w.crossingsAt p).head (List.ne_nil_of_mem hj))
        (w.outgoingSlot ((w.crossingsAt p).head (List.ne_nil_of_mem hj)) p)⟧ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hj
  have hpos : 0 < (w.crossingsAt p).length := by omega
  have hhead := w.pow_statePerm_seifertState_closure_outgoingSlot (List.getElem_mem hpos) i
  simp only [nextCrossing_def, List.formPerm_pow_apply_getElem _ (w.sortedLT_crossingsAt p).nodup,
    zero_add, Nat.mod_eq_of_lt hi] at hhead
  rw [List.head_eq_getElem, ← hhead]
  exact CrossingCircle.mk_eq_mk_iff.2 (.inl (sameCycle_pow_left.2 (SameCycle.refl _ _)))

/-- Strands leaving crossings upwards on two strand positions lie on the same Seifert circle only
when the positions are equal. -/
theorem eq_of_seifertCircle_mk_closure_outgoingSlot_eq {j j' : Fin w.length} {p q : Fin n}
    (hj : j ∈ w.crossingsAt p) (hj' : j' ∈ w.crossingsAt q)
    (h : (⟦w.closure.crossing j (w.outgoingSlot j p)⟧ :
        w.closure.CrossingCircle w.closure.seifertState) =
      ⟦w.closure.crossing j' (w.outgoingSlot j' q)⟧) :
    p = q := by
  rw [seifertCircle_mk_eq_mk_iff_sameCycle _ (by
    rw [orientation_closure_crossing_outgoingSlot, orientation_closure_crossing_outgoingSlot])] at h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [w.pow_statePerm_seifertState_closure_outgoingSlot hj, crossing_closure, crossing_closure,
    (crossingSlotEquiv w.length).apply_eq_iff_eq, Prod.mk.injEq] at hk
  obtain ⟨hk, hslot⟩ := hk
  rw [hk] at hslot
  exact w.eq_of_outgoingSlot_eq (hk ▸ w.pow_nextCrossing_mem_crossingsAt hj k) hj' hslot

/-- Every half-edge of the closure lies on the Seifert circle of the strand leaving its crossing
upwards on the same position. -/
private theorem exists_seifertCircle_mk_closure_eq (x : Fin (4 * w.length)) :
    ∃ (j : Fin w.length) (p : Fin n), j ∈ w.crossingsAt p ∧
      (⟦x⟧ : w.closure.CrossingCircle w.closure.seifertState) =
        ⟦w.closure.crossing j (w.outgoingSlot j p)⟧ := by
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv w.length).surjective x
  have hsmooth (k : Fin 4) :
      (⟦crossingSlotEquiv w.length (j, slotSmoothing true k)⟧ :
        w.closure.CrossingCircle w.closure.seifertState) = ⟦crossingSlotEquiv w.length (j, k)⟧ := by
    have := CrossingCircle.mk_crossing_slotSmoothing (D := w.closure.toPDCode)
      (s := w.closure.seifertState) j k
    rwa [smoothingChoice_seifertState_closure, crossing_closure, crossing_closure] at this
  have h0 := hsmooth 0
  have h3 := hsmooth 3
  rw [show slotSmoothing true 0 = 1 by simp only [slotSmoothing_true]; decide] at h0
  rw [show slotSmoothing true 3 = 2 by simp only [slotSmoothing_true]; decide] at h3
  have hup := w.mem_crossingsAt_strandSucc j
  have hlow := w.mem_crossingsAt_strand j
  fin_cases slot
  · refine ⟨j, _, hup, ?_⟩
    simpa using h0.symm
  · exact ⟨j, _, hup, by simp⟩
  · exact ⟨j, _, hlow, by simp⟩
  · refine ⟨j, _, hlow, ?_⟩
    simpa using h3.symm

/-- The Seifert circle of the closure running along a strand position: the circle through the
strand leaving the lowest crossing on that position upwards, or the crossing-free component on a
position involved in no crossing. -/
private def seifertCircleOfPosition (p : Fin n) : w.closure.SeifertCircle :=
  if h : w.crossingsAt p = [] then .inr (w.crossinglessIndex h)
  else .inl ⟦w.closure.crossing ((w.crossingsAt p).head h)
    (w.outgoingSlot ((w.crossingsAt p).head h) p)⟧

private theorem seifertCircleOfPosition_of_mem {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) :
    w.seifertCircleOfPosition p = .inl ⟦w.closure.crossing j (w.outgoingSlot j p)⟧ := by
  rw [seifertCircleOfPosition]
  split_ifs with h
  · exact absurd h (List.ne_nil_of_mem hj)
  · rw [w.seifertCircle_mk_closure_outgoingSlot hj]

private theorem seifertCircleOfPosition_of_eq_nil {p : Fin n} (h : w.crossingsAt p = []) :
    w.seifertCircleOfPosition p = .inr (w.crossinglessIndex h) := by
  rw [seifertCircleOfPosition]
  split_ifs
  rfl

private theorem bijective_seifertCircleOfPosition :
    Function.Bijective w.seifertCircleOfPosition := by
  constructor
  · intro p q hpq
    by_cases hp : w.crossingsAt p = [] <;> by_cases hq : w.crossingsAt q = []
    · rw [w.seifertCircleOfPosition_of_eq_nil hp, w.seifertCircleOfPosition_of_eq_nil hq,
        Sum.inr.injEq] at hpq
      rw [← w.crossinglessPosition_crossinglessIndex hp, hpq,
        w.crossinglessPosition_crossinglessIndex]
    · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hq
      rw [w.seifertCircleOfPosition_of_eq_nil hp, w.seifertCircleOfPosition_of_mem hj] at hpq
      exact Sum.inr_ne_inl hpq |>.elim
    · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hp
      rw [w.seifertCircleOfPosition_of_mem hj, w.seifertCircleOfPosition_of_eq_nil hq] at hpq
      exact Sum.inl_ne_inr hpq |>.elim
    · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hp
      obtain ⟨j', hj'⟩ := List.exists_mem_of_ne_nil _ hq
      rw [w.seifertCircleOfPosition_of_mem hj, w.seifertCircleOfPosition_of_mem hj',
        Sum.inl.injEq] at hpq
      exact w.eq_of_seifertCircle_mk_closure_outgoingSlot_eq hj hj' hpq
  · rintro (c | c)
    · induction c using Quotient.inductionOn with
      | h x =>
        obtain ⟨j, p, hj, hx⟩ := w.exists_seifertCircle_mk_closure_eq x
        exact ⟨p, by rw [w.seifertCircleOfPosition_of_mem hj, hx]⟩
    · refine ⟨w.crossinglessPosition c, ?_⟩
      rw [w.seifertCircleOfPosition_of_eq_nil (w.crossingsAt_crossinglessPosition c)]
      congr 1
      exact w.crossinglessPosition_strictMono.injective
        (w.crossinglessPosition_crossinglessIndex _)

/-- **The Seifert circles of a closed braid are its strand positions.** The position `p` goes to
the Seifert circle running along it: the circle through the strands leaving its crossings upwards,
or the crossing-free component of the closure on `p` if no letter involves `p`. -/
noncomputable def seifertCircleEquiv : Fin n ≃ w.closure.SeifertCircle :=
  Equiv.ofBijective _ w.bijective_seifertCircleOfPosition

/-- The Seifert circle along a strand position is the circle through the strand leaving any of its
crossings upwards. -/
theorem seifertCircleEquiv_apply_of_mem {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) :
    w.seifertCircleEquiv p = .inl ⟦w.closure.crossing j (w.outgoingSlot j p)⟧ :=
  w.seifertCircleOfPosition_of_mem hj

/-- The Seifert circle along a strand position involved in no crossing is the crossing-free
component of the closure on that position. -/
@[simp]
theorem seifertCircleEquiv_apply_of_eq_nil {p : Fin n} (h : w.crossingsAt p = []) :
    w.seifertCircleEquiv p = .inr (w.crossinglessIndex h) :=
  w.seifertCircleOfPosition_of_eq_nil h

/-- **A closed braid on `n` strands has `n` Seifert circles.** -/
theorem card_seifertCircle_closure : Fintype.card w.closure.SeifertCircle = n := by
  rw [← Fintype.card_congr w.seifertCircleEquiv, Fintype.card_fin]

end BraidWord

end TauCeti
