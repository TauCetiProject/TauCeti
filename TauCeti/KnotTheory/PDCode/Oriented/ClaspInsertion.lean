/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ClaspInsertion

/-!
# Clasp insertion on oriented PD-codes

`TauCeti.PDCode.insertClasp` cuts two arcs of a PD-code open and routes them through a clasp of
two new crossings; when the two arcs border a common face this is the second Reidemeister move.
This file lifts the insertion to oriented codes. Each cut arc keeps its direction, which fixes the
orientations of the eight new half-edges, so the oriented insertion takes no data beyond the
unoriented one.

Whatever the directions of the two arcs, the two new crossings have opposite signs: they have the
same orientation parity, and the same strand is over at both, which with the slot conventions of a
clasp means opposite over-pair indicators. The insertion therefore keeps the writhe. Together with
the invariance of the Kauffman bracket (`TauCeti.PDCode.kauffmanBracket_insertClasp`), this makes
the writhe-normalized Kauffman bracket invariant under the oriented insertion, and in particular
under the oriented second Reidemeister move.

## Main definitions

* `TauCeti.OrientedPDCode.insertClasp`: insert a clasp into two arcs of an oriented code.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_insertClasp_last`: the two new crossings have opposite
  signs.
* `TauCeti.OrientedPDCode.writhe_insertClasp`: the insertion keeps the writhe.
* `TauCeti.OrientedPDCode.normalizedKauffmanBracket_insertClasp`: the writhe-normalized Kauffman
  bracket is invariant under the insertion.
* `TauCeti.OrientedPDCode.mirror_insertClasp` and `TauCeti.OrientedPDCode.reverse_insertClasp`:
  the insertion commutes with reflection and with reversal.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the writhe and the Jones polynomial from the bracket).
-/

public section

namespace TauCeti

namespace OrientedPDCode

open PDCode

variable {n : ℕ}

/-- **Clasp insertion on an oriented PD-code**: the clasp insertion
`TauCeti.PDCode.insertClasp` into the arc ending at `p` and the distinct arc ending at `q`, with
each cut arc keeping its direction. Along the arc ending at `p`, the new half-edges at slots `0`
and `2` of the first new crossing and at slots `1` and `3` of the second alternate between the
orientations `!D.orientation p` and `D.orientation p`, and likewise along the arc ending at `q`
through slots `1` and `3` of the first new crossing and slots `0` and `2` of the second. -/
def insertClasp (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
    (hqe : q ≠ D.edgePair.val p) : OrientedPDCode (n + 2) where
  toPDCode := D.toPDCode.insertClasp p q b hqp hqe
  orientation x :=
    match (halfEdgeSuccEquiv (n + 1)).symm x with
    | .inl y =>
      match (halfEdgeSuccEquiv n).symm y with
      | .inl z => D.orientation z
      | .inr slot => ![!D.orientation p, !D.orientation q, D.orientation p, D.orientation q] slot
    | .inr slot => ![!D.orientation q, !D.orientation p, D.orientation q, D.orientation p] slot
  orientation_edgePair := by
    intro x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot
      · by_cases hxp : x = p
        · subst x
          simp
        by_cases hxe : x = D.edgePair.val p
        · subst x
          simp
        by_cases hxq : x = q
        · subst x
          simp
        by_cases hxe' : x = D.edgePair.val q
        · subst x
          simp
        simp [D.toPDCode.insertClasp_edgePair_inl_inl_of_ne p q b hqp hqe hxp hxe hxq hxe']
      · fin_cases slot <;> simp
    · fin_cases slot <;> simp
  orientation_oppositeCrossingSlot := by
    intro i slot
    induction i using Fin.lastCases with
    | last => fin_cases slot <;> simp [oppositeCrossingSlot_apply]
    | cast i =>
      induction i using Fin.lastCases with
      | last => fin_cases slot <;> simp [oppositeCrossingSlot_apply]
      | cast i => simp
  crossinglessComponents := D.crossinglessComponents
  crossinglessComponents_card := by simp

variable (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
  (hqe : q ≠ D.edgePair.val p)

/-- Forgetting the orientation of the oriented clasp insertion gives the unoriented one. -/
@[simp]
theorem toPDCode_insertClasp :
    (D.insertClasp p q b hqp hqe).toPDCode = D.toPDCode.insertClasp p q b hqp hqe :=
  (rfl)

/-- The oriented clasp insertion keeps the orientation of every old half-edge. -/
@[simp]
theorem orientation_insertClasp_inl_inl (x : Fin (4 * n)) :
    (D.insertClasp p q b hqp hqe).orientation
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) =
      D.orientation x := by
  simp [insertClasp]

/-- The orientations of the slots of the first new crossing: slots `0` and `2` lie on the arc
ending at `p`, slots `1` and `3` on the arc ending at `q`. -/
@[simp]
theorem orientation_insertClasp_inl_inr (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).orientation
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr slot)))) =
      ![!D.orientation p, !D.orientation q, D.orientation p, D.orientation q] slot := by
  simp [insertClasp]

/-- The orientations of the slots of the second new crossing: slots `0` and `2` lie on the arc
ending at `q`, slots `1` and `3` on the arc ending at `p`. -/
@[simp]
theorem orientation_insertClasp_inr (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).orientation (halfEdgeSuccEquiv (n + 1) (.inr slot)) =
      ![!D.orientation q, !D.orientation p, D.orientation q, D.orientation p] slot := by
  simp [insertClasp]

/-- The oriented clasp insertion keeps the oriented crossing-free components. -/
@[simp]
theorem crossinglessComponents_insertClasp :
    (D.insertClasp p q b hqp hqe).crossinglessComponents = D.crossinglessComponents :=
  (rfl)

/-- Every old crossing keeps its sign after the oriented clasp insertion. -/
@[simp]
theorem crossingSign_insertClasp_castSucc_castSucc (i : Fin n) :
    (D.insertClasp p q b hqp hqe).crossingSign i.castSucc.castSucc = D.crossingSign i := by
  simp [crossingSign_def, crossing_apply]

/-- The first new crossing is positive exactly when the parity of the directions of the two cut
arcs is its over-pair indicator `b`. -/
@[simp]
theorem crossingSign_insertClasp_castSucc_last :
    (D.insertClasp p q b hqp hqe).crossingSign (Fin.last n).castSucc =
      if (D.orientation p ^^ D.orientation q) = b then 1 else -1 := by
  simp [crossingSign_def, crossing_apply]

/-- **The two new crossings of an oriented clasp have opposite signs.** -/
@[simp]
theorem crossingSign_insertClasp_last :
    (D.insertClasp p q b hqp hqe).crossingSign (Fin.last (n + 1)) =
      -(D.insertClasp p q b hqp hqe).crossingSign (Fin.last n).castSucc := by
  rw [crossingSign_insertClasp_castSucc_last, crossingSign_def]
  simp only [crossing_apply, toPDCode_insertClasp, crossingSlotEquiv_succ_last,
    insertClasp_crossing_last, orientation_insertClasp_inr, insertClasp_overPair_last]
  generalize D.orientation p = x
  generalize D.orientation q = y
  cases x <;> cases y <;> cases b <;> simp

/-- **The oriented clasp insertion keeps the writhe.** -/
@[simp]
theorem writhe_insertClasp : (D.insertClasp p q b hqp hqe).writhe = D.writhe := by
  rw [writhe_def, writhe_def, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    crossingSign_insertClasp_last]
  simp

/-- **The writhe-normalized Kauffman bracket is invariant under the oriented clasp insertion**,
in particular under the oriented second Reidemeister move. -/
@[simp]
theorem normalizedKauffmanBracket_insertClasp {R : Type*} [CommRing R] (a : Rˣ) :
    (D.insertClasp p q b hqp hqe).normalizedKauffmanBracket a =
      D.normalizedKauffmanBracket a := by
  rw [normalizedKauffmanBracket_def, normalizedKauffmanBracket_def, writhe_insertClasp,
    toPDCode_insertClasp, kauffmanBracket_insertClasp]

/-- Reflecting the oriented clasp insertion inserts the clasp with the other strand over into the
reflected code. -/
@[simp]
theorem mirror_insertClasp :
    (D.insertClasp p q b hqp hqe).mirror =
      D.mirror.insertClasp p q (!b) hqp (by rwa [mirror_toPDCode, mirror_edgePair]) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot <;> simp
    · simp
  · simp

/-- Reversing the oriented clasp insertion inserts the clasp into the reversed code. -/
@[simp]
theorem reverse_insertClasp :
    (D.insertClasp p q b hqp hqe).reverse =
      D.reverse.insertClasp p q b hqp (by rwa [reverse_toPDCode]) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot
      · simp
      · fin_cases slot <;> simp
    · fin_cases slot <;> simp
  · simp

end OrientedPDCode

end TauCeti
