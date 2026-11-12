/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.ClaspInsertion
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert

/-!
# Seifert circles under the second Reidemeister move

Vogel's algorithm turns an oriented link diagram into a closed braid by second Reidemeister moves
between arcs of different Seifert circles, and the number of strands of the resulting braid is the
number of Seifert circles of the diagram. This file computes how the oriented clasp insertion
`TauCeti.OrientedPDCode.insertClasp`, the oriented second Reidemeister move between two arcs,
changes the number of Seifert circles.

Let the clasp be inserted into the arc ending at the half-edge `p` and the arc ending at `q`. Both
new crossings get the same Seifert smoothing, selected by the parity of the orientations of `p` and
`q`. In terms of states, the Seifert state at the first new crossing compares that parity with the
over-pair indicator of the clasp (`TauCeti.OrientedPDCode.seifertState_insertClasp_castSucc_last`),
and the second new crossing, of the opposite sign, gets the opposite state
(`TauCeti.OrientedPDCode.seifertState_insertClasp_last`).

* If `p` and `q` have the same orientation, the two arcs run through the clasp in parallel, and
  the Seifert smoothing of the clasp gives back the two arcs: the Seifert circles are unchanged in
  number (`TauCeti.OrientedPDCode.card_seifertCircle_insertClasp_of_orientation_eq`).
* If they have opposite orientations, the arcs run through the clasp antiparallel. The Seifert
  smoothing then cuts off a small circle inside the clasp, and reconnects the cut arcs, `p` to `q`
  and the other end of one to the other end of the other. Read as two transpositions of the
  Seifert traversal (`TauCeti.PerfectMatching.reconnect_val_eq_mul_swap_mul_swap`), this
  reconnection merges the Seifert circles through the two arcs when they are different, and splits
  their common circle in two otherwise.

So the number of Seifert circles is unchanged, unless the two arcs are antiparallel on one Seifert
circle, when it goes up by two (`TauCeti.OrientedPDCode.card_seifertCircle_insertClasp`). In
particular a clasp between arcs of two different Seifert circles, as in a move of Vogel's
algorithm, keeps the number of Seifert circles
(`TauCeti.OrientedPDCode.card_seifertCircle_insertClasp_of_mk_ne`).

## Main results

* `TauCeti.OrientedPDCode.card_seifertCircle_insertClasp`: the number of Seifert circles after the
  oriented clasp insertion.
* `TauCeti.OrientedPDCode.card_seifertCircle_insertClasp_of_orientation_eq`: a parallel clasp
  keeps the number of Seifert circles.
* `TauCeti.OrientedPDCode.card_seifertCircle_insertClasp_of_mk_ne`: a clasp between two different
  Seifert circles keeps their number.

## References

* P. Vogel, *Representation of links by braids: a new algorithm*, Comment. Math. Helv. 65 (1990),
  104-113.
* S. Yamada, *The minimal number of Seifert circles equals the braid index of a link*, Invent.
  Math. 89 (1987), 347-356.
-/

public section

namespace TauCeti

namespace OrientedPDCode

open Equiv Equiv.Perm PDCode

variable {n : ℕ} (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
  (hqe : q ≠ D.edgePair.val p)

/-! ### The Seifert state of a clasp -/

/-- At the old crossings, the Seifert state of the oriented clasp insertion is that of the old
code. -/
@[simp]
theorem seifertState_insertClasp_castSucc_castSucc (i : Fin n) :
    (D.insertClasp p q b hqp hqe).seifertState i.castSucc.castSucc = D.seifertState i := by
  rw [Bool.eq_iff_iff, seifertState_eq_true_iff, seifertState_eq_true_iff,
    crossingSign_insertClasp_castSucc_castSucc]

/-- At the first new crossing, the Seifert state of the oriented clasp insertion selects the
`A`-smoothing exactly when the parity of the orientations of `p` and `q` is the over-pair
indicator `b`. -/
@[simp]
theorem seifertState_insertClasp_castSucc_last :
    (D.insertClasp p q b hqp hqe).seifertState (Fin.last n).castSucc =
      ((D.orientation p ^^ D.orientation q) == b) := by
  rw [Bool.eq_iff_iff, seifertState_eq_true_iff, crossingSign_insertClasp_castSucc_last]
  split_ifs with h <;> simp [h]

/-- At the second new crossing, the Seifert state of the oriented clasp insertion makes the other
choice. -/
@[simp]
theorem seifertState_insertClasp_last :
    (D.insertClasp p q b hqp hqe).seifertState (Fin.last (n + 1)) =
      !((D.orientation p ^^ D.orientation q) == b) := by
  rw [Bool.eq_iff_iff, seifertState_eq_true_iff, crossingSign_insertClasp_last,
    crossingSign_insertClasp_castSucc_last]
  split_ifs with h <;> simp [h]

/-! ### Counting the Seifert circles -/

/-- Off the orientation of `p`, the Seifert traversal agrees with the traversal after the
transposition of `p` with the other end of the arc ending at `q`, which has the orientation of `p`
when `p` and `q` have opposite orientations. -/
private theorem pow_mul_swap_apply_of_orientation_ne (hpq : D.orientation p ≠ D.orientation q)
    {x : Fin (4 * n)} (hx : D.orientation x ≠ D.orientation p) (k : ℕ) :
    ((D.statePerm D.seifertState * swap p (D.edgePair.val q)) ^ k) x =
      (D.statePerm D.seifertState ^ k) x := by
  have hq : D.orientation (D.edgePair.val q) = D.orientation p := by
    rw [orientation_edgePair, Bool.not_eq]
    exact Ne.symm hpq
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : D.orientation ((D.statePerm D.seifertState ^ k) x) = D.orientation x :=
      (D.orientation_eq_of_sameCycle_statePerm_seifertState
        (Perm.sameCycle_pow_right.2 (SameCycle.refl _ x))).symm
    have hne₁ : (D.statePerm D.seifertState ^ k) x ≠ p := fun h ↦ hx (by rw [← hk, h])
    have hne₂ : (D.statePerm D.seifertState ^ k) x ≠ D.edgePair.val q := fun h ↦
      hx (by rw [← hk, h, hq])
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply, Perm.mul_apply,
      swap_apply_of_ne_of_ne hne₁ hne₂]

/-- The transposition of `p` with the other end of the arc ending at `q` does not change which
half-edges of the other orientation lie on one directed orbit of the Seifert traversal. -/
private theorem sameCycle_mul_swap_iff_of_orientation_ne (hpq : D.orientation p ≠ D.orientation q)
    {x y : Fin (4 * n)} (hx : D.orientation x ≠ D.orientation p) :
    (D.statePerm D.seifertState * swap p (D.edgePair.val q)).SameCycle x y ↔
      (D.statePerm D.seifertState).SameCycle x y := by
  constructor <;> intro h <;> obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  · rw [D.pow_mul_swap_apply_of_orientation_ne p q hpq hx]
    exact Perm.sameCycle_pow_right.2 (SameCycle.refl _ x)
  · rw [← D.pow_mul_swap_apply_of_orientation_ne p q hpq hx]
    exact Perm.sameCycle_pow_right.2 (SameCycle.refl _ x)

/-- For `p` and `q` of opposite orientations, `p` and `q` lie on one Seifert circle exactly when
`p` and the other end of the arc ending at `q` lie on one directed orbit of the Seifert traversal,
and exactly when `q` and the other end of the arc ending at `p` do. -/
private theorem mk_eq_mk_iff_of_orientation_ne (hpq : D.orientation p ≠ D.orientation q) :
    ((⟦p⟧ : D.CrossingCircle D.seifertState) = ⟦q⟧ ↔
      (D.statePerm D.seifertState).SameCycle p (D.edgePair.val q)) ∧
    ((⟦p⟧ : D.CrossingCircle D.seifertState) = ⟦q⟧ ↔
      (D.statePerm D.seifertState).SameCycle q (D.edgePair.val p)) := by
  have hp : D.orientation p = D.orientation (D.edgePair.val q) := by
    rw [orientation_edgePair, Bool.eq_not]
    exact hpq
  have hq : D.orientation q = D.orientation (D.edgePair.val p) := by
    rw [orientation_edgePair, Bool.eq_not]
    exact Ne.symm hpq
  constructor
  · rw [← D.seifertCircle_mk_eq_mk_iff_sameCycle hp, CrossingCircle.mk_edgePair]
  · rw [← D.seifertCircle_mk_eq_mk_iff_sameCycle hq, CrossingCircle.mk_edgePair, eq_comm]

include hqe in
/-- **Directed Seifert orbits after reconnecting antiparallel arcs.** For `p` and `q` of opposite
orientations, reconnecting the arcs ending at `p` and at `q` in the Seifert traversal adds two
directed orbits when they lie on one Seifert circle, and removes two otherwise. -/
private theorem orbitCount_reconnect_of_orientation_ne (hpq : D.orientation p ≠ D.orientation q) :
    orbitCount (D.smoothingTurn (D.smoothingChoice D.seifertState) *
        (D.edgePair.reconnect p q).val) + 2 =
      orbitCount (D.statePerm D.seifertState) +
        if (⟦p⟧ : D.CrossingCircle D.seifertState) = ⟦q⟧ then 4 else 0 := by
  have hpe : p ≠ D.edgePair.val q := fun h ↦ hqe (by rw [h, D.edgePair.apply_apply])
  have hqp' : D.orientation q ≠ D.orientation p := Ne.symm hpq
  rw [PerfectMatching.reconnect_val_eq_mul_swap_mul_swap, ← mul_assoc, ← mul_assoc,
    ← statePerm_def]
  obtain ⟨h₁, h₂⟩ := D.mk_eq_mk_iff_of_orientation_ne p q hpq
  split_ifs with h
  · have hc₁ := orbitCount_mul_swap_of_sameCycle hpe (h₁.1 h)
    have hc₂ := orbitCount_mul_swap_of_sameCycle hqe
      ((D.sameCycle_mul_swap_iff_of_orientation_ne p q hpq hqp').2 (h₂.1 h))
    omega
  · have hc₁ := orbitCount_mul_swap_add_one_of_not_sameCycle (mt h₁.2 h)
    have hc₂ := orbitCount_mul_swap_add_one_of_not_sameCycle
      (mt (D.sameCycle_mul_swap_iff_of_orientation_ne p q hpq hqp').1 (mt h₂.2 h))
    omega

/-- **Seifert circles under the second Reidemeister move.** The oriented clasp insertion into the
arcs ending at `p` and at `q` keeps the number of Seifert circles, unless `p` and `q` have opposite
orientations and lie on one Seifert circle, when it adds two. -/
theorem card_seifertCircle_insertClasp :
    Fintype.card (D.insertClasp p q b hqp hqe).SeifertCircle =
      Fintype.card D.SeifertCircle +
        if D.orientation p ≠ D.orientation q ∧
          (⟦p⟧ : D.CrossingCircle D.seifertState) = ⟦q⟧ then 2 else 0 := by
  have hinit : Fin.init (Fin.init (D.insertClasp p q b hqp hqe).seifertState) = D.seifertState :=
    funext fun i ↦ by simp [Fin.init]
  have hc := D.toPDCode.two_mul_card_crossingCircle D.seifertState
  rw [card_resolvedCircle, card_resolvedCircle, stateLoopCount_def (D := D.toPDCode),
    toPDCode_insertClasp, stateLoopCount_insertClasp, hinit,
    seifertState_insertClasp_castSucc_last, seifertState_insertClasp_last]
  -- Both new crossings carry the Seifert smoothing `D.orientation p ^^ D.orientation q`.
  by_cases hpq : D.orientation p = D.orientation q
  · rw [hpq, Bool.xor_self]
    cases b <;> simp [stateLoopCount_def]
  · have ho := D.orbitCount_reconnect_of_orientation_ne p q hqe hpq
    have hx : (D.orientation p ^^ D.orientation q) = true := by
      simpa using hpq
    have hif : (D.orientation p ≠ D.orientation q ∧
        (⟦p⟧ : D.CrossingCircle D.seifertState) = ⟦q⟧) ↔
        (⟦p⟧ : D.CrossingCircle D.seifertState) = ⟦q⟧ := and_iff_right hpq
    rw [hx, if_congr hif rfl rfl]
    cases b <;> simp only [Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, and_self, ↓reduceIte] <;>
    split_ifs at ho ⊢ <;> omega

/-- **A parallel clasp keeps the number of Seifert circles**: the oriented clasp insertion into
arcs ending at half-edges of the same orientation. -/
theorem card_seifertCircle_insertClasp_of_orientation_eq (h : D.orientation p = D.orientation q) :
    Fintype.card (D.insertClasp p q b hqp hqe).SeifertCircle = Fintype.card D.SeifertCircle := by
  rw [card_seifertCircle_insertClasp]
  simp [h]

/-- **A clasp between two different Seifert circles keeps the number of Seifert circles**, whatever
the orientations of its arcs. This is the count behind Vogel's algorithm, whose moves are such
clasps. -/
theorem card_seifertCircle_insertClasp_of_mk_ne
    (h : (⟦p⟧ : D.CrossingCircle D.seifertState) ≠ ⟦q⟧) :
    Fintype.card (D.insertClasp p q b hqp hqe).SeifertCircle = Fintype.card D.SeifertCircle := by
  rw [card_seifertCircle_insertClasp]
  simp [h]

end OrientedPDCode

end TauCeti
