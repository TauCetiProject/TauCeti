/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Basic

/-!
# Seifert circles of an oriented PD-code

Smoothing every crossing of an oriented diagram in the way that respects the orientation, joining
each incoming strand to the adjacent outgoing one, leaves a disjoint union of oriented circles: the
**Seifert circles** of the diagram. They are the starting point of Seifert's algorithm, which caps
them off by discs and joins the discs by a half-twisted band at each crossing to obtain an oriented
surface bounded by the link, and of the algorithms of Yamada and Vogel, which turn a diagram into a
closed braid by manipulating its Seifert circles.

At a crossing whose slots are read counterclockwise, the two local strands occupy the opposite
slots `0`, `2` and `1`, `3`, and the orientation reverses between opposite slots. The
orientation-respecting smoothing joins each slot to the adjacent slot of the other orientation:
it is `TauCeti.PDCode.slotSmoothing` applied to the parity of the orientations at the slots `0`
and `1`. In the convention of the Kauffman bracket this is the `A`-smoothing at a positive
crossing and the `B`-smoothing at a negative one, so the Seifert circles are the circles
`TauCeti.PDCode.ResolvedCircle` of the state `TauCeti.OrientedPDCode.seifertState`, and the
crossing-free components of the diagram are Seifert circles of their own. The Seifert state is the
only state whose smoothing joins half-edges of opposite orientations at every crossing
(`TauCeti.OrientedPDCode.eq_seifertState_iff`).

An arc of the diagram also joins two half-edges of opposite orientations, so the traversal of the
Seifert smoothing (`TauCeti.PDCode.statePerm`) preserves the orientation of half-edges. Hence two
half-edges with the same orientation lie on one Seifert circle exactly when they lie on one
directed traversal orbit: the orientation of the diagram orients each Seifert circle coherently,
and that circle, travelled in this direction, is a single orbit of the traversal.

## Main definitions

* `TauCeti.OrientedPDCode.seifertState`: the state selecting the `A`-smoothing at the positive
  crossings and the `B`-smoothing at the negative ones.
* `TauCeti.OrientedPDCode.SeifertCircle`: the Seifert circles of an oriented PD-code.

## Main results

* `TauCeti.OrientedPDCode.smoothingChoice_seifertState`: the Seifert state smooths each crossing
  by the local smoothing selected by the orientations at its slots `0` and `1`.
* `TauCeti.OrientedPDCode.orientation_smoothingTurn_seifertState` and
  `TauCeti.OrientedPDCode.eq_seifertState_iff`: the Seifert smoothing joins half-edges of opposite
  orientations, and it is the only smoothing doing so.
* `TauCeti.OrientedPDCode.orientation_statePerm_seifertState`: the traversal of the Seifert
  smoothing preserves the orientation of half-edges.
* `TauCeti.OrientedPDCode.seifertCircle_mk_eq_mk_iff_sameCycle`: two half-edges of the same
  orientation lie on one Seifert circle exactly when they lie on one directed traversal orbit.

## References

* H. Seifert, *Über das Geschlecht von Knoten*, Math. Ann. 110 (1935), 571-592.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 2 (the
  Seifert circles of an oriented diagram in the proof of Theorem 2.2).
* S. Yamada, *The minimal number of Seifert circles equals the braid index of a link*, Invent.
  Math. 89 (1987), 347-356.
* P. Vogel, *Representation of links by braids: a new algorithm*, Comment. Math. Helv. 65 (1990),
  104-113.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm PDCode

namespace OrientedPDCode

variable {n : ℕ} (D : OrientedPDCode n)

/-! ### The Seifert state -/

/-- The **Seifert state** of an oriented PD-code: the `A`-smoothing (`true`) at the positive
crossings and the `B`-smoothing (`false`) at the negative ones. Its smoothing joins each incoming
strand at a crossing to the adjacent outgoing one, and its circles are the Seifert circles. -/
def seifertState (i : Fin n) : Bool :=
  decide (D.crossingSign i = 1)

/-- The Seifert state selects the `A`-smoothing exactly at the positive crossings. -/
@[simp]
theorem seifertState_eq_true_iff {i : Fin n} : D.seifertState i = true ↔ D.crossingSign i = 1 :=
  decide_eq_true_iff

/-- The Seifert state selects the `B`-smoothing exactly at the negative crossings. -/
@[simp]
theorem seifertState_eq_false_iff {i : Fin n} :
    D.seifertState i = false ↔ D.crossingSign i = -1 := by
  rw [seifertState, decide_eq_false_iff_not]
  rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> simp [h]

/-- **The Seifert smoothing.** At each crossing the Seifert state selects the local smoothing
`TauCeti.PDCode.slotSmoothing` of the parity of the orientations at the slots `0` and `1`: the
smoothing joining slot `0` to the adjacent slot of the other orientation. -/
@[simp]
theorem smoothingChoice_seifertState (i : Fin n) :
    D.smoothingChoice D.seifertState i =
      Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) := by
  rcases D.crossingSign_eq_one_or_neg_one i with h | h
  · rw [smoothingChoice_of_true _ (D.seifertState_eq_true_iff.2 h),
      (D.crossingSign_eq_one_iff i).1 h]
  · rw [smoothingChoice_of_false _ (D.seifertState_eq_false_iff.2 h)]
    have h' := (D.crossingSign_eq_neg_one_iff i).1 h
    clear h
    generalize D.orientation (D.crossing i 0) = a at *
    generalize D.orientation (D.crossing i 1) = b at *
    revert h'
    cases a <;> cases b <;> cases D.overPair i <;> decide

/-- Reversing every component orientation does not change the Seifert state. -/
@[simp]
theorem seifertState_reverse : D.reverse.seifertState = D.seifertState := by
  funext i
  simp [seifertState]

/-- Reflection exchanges the two smoothings selected by the Seifert state. -/
@[simp]
theorem seifertState_mirror (i : Fin n) : D.mirror.seifertState i = !D.seifertState i := by
  rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> simp [seifertState, h]

/-- Reflection does not change the Seifert smoothing itself, so a diagram and its mirror image have
the same Seifert circles. -/
theorem smoothingChoice_mirror_seifertState :
    D.mirror.smoothingChoice D.mirror.seifertState = D.smoothingChoice D.seifertState := by
  funext i
  rw [smoothingChoice_seifertState, smoothingChoice_seifertState, mirror_orientation,
    mirror_toPDCode, PDCode.crossing_mirror, PDCode.crossing_mirror]

/-- Relabelling reads the Seifert state at the old crossing name. -/
@[simp]
theorem seifertState_relabel {m : ℕ} (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).seifertState = D.seifertState ∘ cross.symm := by
  funext i
  simp [seifertState, crossingSign_relabel]

/-! ### Orientations along the Seifert smoothing -/

/-- At slot level: when the orientations at the four slots of a crossing are `a`, `b`, `!a`, `!b`,
the smoothing selected by the parity of `a` and `b` joins slots of opposite orientations. -/
private theorem slotSmoothing_xor_orientation (a b : Bool) (k : Fin 4) :
    ![a, b, !a, !b] (slotSmoothing (Bool.xor a b) k) = !(![a, b, !a, !b] k) := by
  cases a <;> cases b <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_false,
    Bool.not_true, slotSmoothing_true, slotSmoothing_false] <;> revert k <;> decide

/-- At slot level: the other smoothing joins slot `0` to a slot of the same orientation. -/
private theorem slotSmoothing_not_xor_orientation (a b : Bool) :
    ![a, b, !a, !b] (slotSmoothing (!Bool.xor a b) 0) = a := by
  cases a <;> cases b <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_false,
    Bool.not_true, slotSmoothing_true, slotSmoothing_false] <;> decide

/-- **The Seifert smoothing joins half-edges of opposite orientations**: at every crossing it joins
the end of an incoming strand to the start of an outgoing one. -/
@[simp]
theorem orientation_smoothingTurn_seifertState (h : Fin (4 * n)) :
    D.orientation (D.smoothingTurn (D.smoothingChoice D.seifertState) h) = !D.orientation h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨i, k⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [smoothingTurn_crossing, smoothingChoice_seifertState, ← crossing_apply,
    D.orientation_crossing_eq i (slotSmoothing _ k), D.orientation_crossing_eq i k]
  exact slotSmoothing_xor_orientation _ _ k

/-- **The Seifert state is the only state whose smoothing joins half-edges of opposite
orientations** at every crossing. -/
theorem eq_seifertState_iff {s : Fin n → Bool} :
    s = D.seifertState ↔
      ∀ h, D.orientation (D.smoothingTurn (D.smoothingChoice s) h) = !D.orientation h := by
  refine ⟨fun hs ↦ hs ▸ D.orientation_smoothingTurn_seifertState, fun hs ↦ funext fun i ↦ ?_⟩
  by_contra hne
  have hi := hs (D.crossing i 0)
  rw [crossing_apply, smoothingTurn_crossing,
    D.toPDCode.smoothingChoice_eq_not_smoothingChoice (Ne.symm hne), smoothingChoice_seifertState,
    ← crossing_apply, D.orientation_crossing_eq i (slotSmoothing _ 0),
    slotSmoothing_not_xor_orientation] at hi
  cases D.orientation (D.crossing i 0) <;> simp at hi

/-- **The traversal of the Seifert smoothing preserves orientations**: crossing an arc and then
following the Seifert smoothing leads from an outgoing half-edge to an outgoing one, and from an
incoming half-edge to an incoming one. -/
theorem orientation_statePerm_seifertState (h : Fin (4 * n)) :
    D.orientation (D.statePerm D.seifertState h) = D.orientation h := by
  rw [statePerm_apply, orientation_smoothingTurn_seifertState, orientation_edgePair, Bool.not_not]

/-- Two half-edges on one directed traversal orbit of the Seifert smoothing have the same
orientation. -/
theorem orientation_eq_of_sameCycle_statePerm_seifertState {x y : Fin (4 * n)}
    (h : (D.statePerm D.seifertState).SameCycle x y) : D.orientation x = D.orientation y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Perm.mul_apply, orientation_statePerm_seifertState, ih]

/-! ### Seifert circles -/

/-- The **Seifert circles** of an oriented PD-code: the circles of the smoothing selected by the
Seifert state. Those meeting a crossing are the classes of half-edges joined by arcs and by the
Seifert smoothing; each crossing-free component of the code is a Seifert circle of its own. -/
abbrev SeifertCircle : Type :=
  D.ResolvedCircle D.seifertState

/-- **The orientation orients each Seifert circle coherently.** Two half-edges of the same
orientation lie on one Seifert circle exactly when they lie on one directed traversal orbit of the
Seifert smoothing. -/
theorem seifertCircle_mk_eq_mk_iff_sameCycle {x y : Fin (4 * n)}
    (hxy : D.orientation x = D.orientation y) :
    (⟦x⟧ : D.CrossingCircle D.seifertState) = ⟦y⟧ ↔
      (D.statePerm D.seifertState).SameCycle x y := by
  refine CrossingCircle.mk_eq_mk_iff.trans ⟨fun h ↦ h.resolve_right fun h' ↦ ?_, Or.inl⟩
  have := D.orientation_eq_of_sameCycle_statePerm_seifertState h'
  rw [orientation_edgePair, ← hxy] at this
  cases hx : D.orientation x <;> simp [hx] at this

end OrientedPDCode

end TauCeti
