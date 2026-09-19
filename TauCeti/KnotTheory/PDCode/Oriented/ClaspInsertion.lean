/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ClaspInsertion

/-!
# Oriented algebraic clasp insertion

The orientations of two distinct arcs extend across `PDCode.insertClasp`. The two new
crossings have opposite signs, for either relative orientation of the strands and either
choice of over-strand. Consequently the writhe and the writhe-normalized Kauffman bracket
are unchanged. This is the oriented algebraic calculation used for the second Reidemeister
move in the construction of the Jones polynomial.

As with the underlying insertion, no planar locality is asserted: a `PDCode` carries no
witness that the selected arcs bound a common local disk. The operation applies to two
distinct arcs incident to existing crossings; crossing-free circles are retained unchanged.

The construction follows the orientation-extension pattern of
`OrientedPDCode.reidemeisterOne`. The mathematical conventions follow L. H. Kauffman,
*State models and the Jones polynomial*, Topology 26 (1987), 395–407, and W. B. R. Lickorish,
*An Introduction to Knot Theory*, Chapter 3, Lemma 3.3 and Theorem 3.5.
-/

public section

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

private def claspOrientation (o p : Bool) : Fin 4 → Bool := ![!o, !p, o, p]

private theorem claspOrientation_oppositeCrossingSlot (o p : Bool) (slot : Fin 4) :
    claspOrientation o p (PDCode.oppositeCrossingSlot slot) =
      !claspOrientation o p slot := by
  have hopposite : PDCode.oppositeCrossingSlot slot = slot + 2 := by
    apply Fin.ext
    exact PDCode.oppositeCrossingSlot_apply slot
  rw [hopposite]
  fin_cases slot <;> simp [claspOrientation]

/-- Extend the orientations of two distinct arcs across their algebraic clasp insertion.
The Boolean `b` selects the over-strand as in `PDCode.insertClasp`. -/
def insertClasp (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
    (hqe : q ≠ D.edgePair.val p) : OrientedPDCode (n + 2) where
  toPDCode := D.toPDCode.insertClasp p q b hqp hqe
  orientation x :=
    match (PDCode.halfEdgeSuccEquiv (n + 1)).symm x with
    | .inl y =>
      match (PDCode.halfEdgeSuccEquiv n).symm y with
      | .inl z => D.orientation z
      | .inr slot => claspOrientation (D.orientation p) (D.orientation q) slot
    | .inr slot => claspOrientation (D.orientation q) (D.orientation p) slot
  orientation_edgePair := by
    intro x
    obtain ⟨x, rfl⟩ := (PDCode.halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (PDCode.halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot
      · by_cases hxp : x = p
        · subst x
          simp [claspOrientation]
        · by_cases hxe : x = D.edgePair.val p
          · subst x
            simp [claspOrientation]
          · by_cases hxq : x = q
            · subst x
              simp [claspOrientation]
            · by_cases hxe' : x = D.edgePair.val q
              · subst x
                simp [claspOrientation]
              · rw [D.toPDCode.insertClasp_edgePair_inl_inl_of_ne p q b hqp hqe
                  hxp hxe hxq hxe']
                simp
      · fin_cases slot <;> simp [claspOrientation]
    · fin_cases slot <;> simp [claspOrientation]
  orientation_oppositeCrossingSlot := by
    intro i slot
    induction i using Fin.lastCases with
    | last =>
      simpa using claspOrientation_oppositeCrossingSlot (D.orientation q) (D.orientation p) slot
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        simpa using claspOrientation_oppositeCrossingSlot (D.orientation p) (D.orientation q) slot
      | cast i => simp
  crossinglessComponents := D.crossinglessComponents
  crossinglessComponents_card := by simp

variable (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool)
  (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)

/-- Forgetting orientation recovers the existing algebraic clasp insertion. -/
@[simp] theorem toPDCode_insertClasp :
    (D.insertClasp p q b hqp hqe).toPDCode = D.toPDCode.insertClasp p q b hqp hqe := (rfl)

/-- Every old half-edge retains its orientation. -/
@[simp] theorem orientation_insertClasp_inl_inl (x : Fin (4 * n)) :
    (D.insertClasp p q b hqp hqe).orientation
        (PDCode.halfEdgeSuccEquiv (n + 1) (.inl (PDCode.halfEdgeSuccEquiv n (.inl x)))) =
      D.orientation x := by
  simp [insertClasp]

/-- The slot orientations of the first new crossing, in counterclockwise order. -/
@[simp] theorem orientation_insertClasp_inl_inr (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).orientation
        (PDCode.halfEdgeSuccEquiv (n + 1) (.inl (PDCode.halfEdgeSuccEquiv n (.inr slot)))) =
      ![!D.orientation p, !D.orientation q, D.orientation p, D.orientation q] slot := by
  simp [insertClasp, claspOrientation]

/-- The slot orientations of the second new crossing, in counterclockwise order. -/
@[simp] theorem orientation_insertClasp_inr (slot : Fin 4) :
    (D.insertClasp p q b hqp hqe).orientation
        (PDCode.halfEdgeSuccEquiv (n + 1) (.inr slot)) =
      ![!D.orientation q, !D.orientation p, D.orientation q, D.orientation p] slot := by
  simp [insertClasp, claspOrientation]

/-- The oriented crossing-free components are unchanged. -/
@[simp] theorem crossinglessComponents_insertClasp :
    (D.insertClasp p q b hqp hqe).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Reflection commutes with clasp insertion, exchanging the over-strand. -/
@[simp] theorem mirror_insertClasp :
    (D.insertClasp p q b hqp hqe).mirror =
      D.mirror.insertClasp p q (!b) hqp (by rwa [mirror_edgePair]) := by
  apply ext
  · simp
  · simp [insertClasp]
  · simp

/-- Reversing every component commutes with clasp insertion. -/
@[simp] theorem reverse_insertClasp :
    (D.insertClasp p q b hqp hqe).reverse =
      D.reverse.insertClasp p q b hqp (by rwa [reverse_toPDCode]) := by
  apply ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (PDCode.halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | slot
    · obtain ⟨x, rfl⟩ := (PDCode.halfEdgeSuccEquiv n).surjective x
      rcases x with x | slot
      · simp
      · fin_cases slot <;> simp
    · fin_cases slot <;> simp
  · simp

/-- Every old crossing retains its sign. -/
@[simp] theorem crossingSign_insertClasp_castSucc_castSucc (i : Fin n) :
    (D.insertClasp p q b hqp hqe).crossingSign i.castSucc.castSucc = D.crossingSign i := by
  rcases D.crossingSign_eq_one_or_neg_one i with hi | hi
  · rw [hi]
    apply (crossingSign_eq_one_iff _ _).mpr
    simpa using (D.crossingSign_eq_one_iff i).mp hi
  · rw [hi]
    apply (crossingSign_eq_neg_one_iff _ _).mpr
    simpa using (D.crossingSign_eq_neg_one_iff i).mp hi

/-- The first new crossing is positive exactly when the old endpoint orientation parity
agrees with its over-pair indicator. -/
@[simp] theorem crossingSign_insertClasp_castSucc_last :
    (D.insertClasp p q b hqp hqe).crossingSign (Fin.last n).castSucc =
      if Bool.xor (D.orientation p) (D.orientation q) = b then 1 else -1 := by
  split_ifs with h
  · apply (crossingSign_eq_one_iff _ _).mpr
    simpa using h
  · apply (crossingSign_eq_neg_one_iff _ _).mpr
    simpa using h

/-- The second new crossing has the opposite sign to the first. -/
@[simp] theorem crossingSign_insertClasp_last :
    (D.insertClasp p q b hqp hqe).crossingSign (Fin.last (n + 1)) =
      -(if Bool.xor (D.orientation p) (D.orientation q) = b then 1 else -1) := by
  cases hp : D.orientation p <;> cases hq : D.orientation q <;> cases b <;>
    simp [hp, hq]

/-- Algebraic clasp insertion preserves writhe: its two new crossing signs cancel. -/
@[simp] theorem writhe_insertClasp :
    (D.insertClasp p q b hqp hqe).writhe = D.writhe := by
  rw [writhe_def, writhe_def, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp

/-- The writhe-normalized Kauffman bracket is invariant under oriented algebraic clasp
insertion, for either relative strand orientation and either over-strand. -/
@[simp] theorem normalizedKauffmanBracket_insertClasp {R : Type*} [CommRing R] (a : Rˣ) :
    (D.insertClasp p q b hqp hqe).normalizedKauffmanBracket a =
      D.normalizedKauffmanBracket a := by
  simp [normalizedKauffmanBracket_def]

end TauCeti.OrientedPDCode
