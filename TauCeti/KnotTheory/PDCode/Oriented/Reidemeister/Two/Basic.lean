/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.Two.Basic

/-!
# Oriented circle-and-arc Reidemeister clasps

Lift `PDCode.insertCircleClasp` to oriented diagrams, retaining the direction of the
chosen arc and specifying the new circle's direction. The new crossings have opposite
signs, so the writhe is unchanged. The normalized Kauffman bracket and Jones polynomial
agree with those of the original diagram with that oriented circle adjoined.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 3,
  Lemma 3.3 and Theorem 3.5.
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

namespace TauCeti.OrientedPDCode

open PDCode

variable {n : ℕ}

/-- Push a new oriented circle across the arc ending at `p`. The circle's direction is
`o`, and the first crossing has over-pair indicator `b`. -/
def insertCircleClasp (D : OrientedPDCode n) (p : Fin (4 * n)) (o b : Bool) :
    OrientedPDCode (n + 2) where
  toPDCode := D.toPDCode.insertCircleClasp p b
  orientation x :=
    match (halfEdgeSuccEquiv (n + 1)).symm x with
    | .inl y =>
      match (halfEdgeSuccEquiv n).symm y with
      | .inl z => D.orientation z
      | .inr s => ![!D.orientation p, !o, D.orientation p, o] s
    | .inr s => ![!o, !D.orientation p, o, D.orientation p] s
  orientation_edgePair := by
    intro x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | s
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | s
      · by_cases hx : x = p
        · subst x; simp [-crossing_apply]
        by_cases hx' : x = D.edgePair.val p
        · subst x; simp [-crossing_apply]
        simp [D.toPDCode.insertCircleClasp_edgePair_old p b hx hx']
      · rw [D.toPDCode.insertCircleClasp_edgePair_first]
        fin_cases s <;> simp [-crossing_apply]
    · rw [D.toPDCode.insertCircleClasp_edgePair_second]
      fin_cases s <;> simp [-crossing_apply]
  orientation_oppositeCrossingSlot := by
    intro i s
    induction i using Fin.lastCases with
    | last =>
      simp only [crossingSlotEquiv_succ_last, PDCode.insertCircleClasp_crossing_last]
      fin_cases s <;> simp [oppositeCrossingSlot_apply]
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        simp only [crossingSlotEquiv_succ_castSucc, crossingSlotEquiv_succ_last,
          PDCode.insertCircleClasp_crossing_castSucc_last]
        fin_cases s <;> simp [oppositeCrossingSlot_apply]
      | cast i =>
        simp only [crossingSlotEquiv_succ_castSucc,
          PDCode.insertCircleClasp_crossing_castSucc_castSucc]
        simp
  crossinglessComponents := D.crossinglessComponents
  crossinglessComponents_card := by simp

variable (D : OrientedPDCode n) (p : Fin (4 * n)) (o b : Bool)

/-- Forgetting orientation gives the underlying circle-and-arc clasp. -/
@[simp] theorem toPDCode_insertCircleClasp :
    (D.insertCircleClasp p o b).toPDCode = D.toPDCode.insertCircleClasp p b := (rfl)

/-- The insertion retains the orientation of every old half-edge. -/
@[simp] theorem orientation_insertCircleClasp_old (x : Fin (4 * n)) :
    (D.insertCircleClasp p o b).orientation
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inl x)))) =
      D.orientation x := by simp [insertCircleClasp]

/-- Orientations at the first new crossing. -/
@[simp] theorem orientation_insertCircleClasp_first (s : Fin 4) :
    (D.insertCircleClasp p o b).orientation
        (halfEdgeSuccEquiv (n + 1) (.inl (halfEdgeSuccEquiv n (.inr s)))) =
      ![!D.orientation p, !o, D.orientation p, o] s := by
  simp [insertCircleClasp]

/-- Orientations at the second new crossing. -/
@[simp] theorem orientation_insertCircleClasp_second (s : Fin 4) :
    (D.insertCircleClasp p o b).orientation
        (halfEdgeSuccEquiv (n + 1) (.inr s)) =
      ![!o, !D.orientation p, o, D.orientation p] s := by
  simp [insertCircleClasp]

/-- Existing crossing-free components retain their chosen directions. -/
@[simp] theorem crossinglessComponents_insertCircleClasp :
    (D.insertCircleClasp p o b).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Every old crossing keeps its sign. -/
@[simp] theorem crossingSign_insertCircleClasp_castSucc_castSucc (i : Fin n) :
    (D.insertCircleClasp p o b).crossingSign i.castSucc.castSucc = D.crossingSign i := by
  simp [crossingSign_def, crossing_apply]

/-- The two new crossings have opposite signs. -/
@[simp] theorem crossingSign_insertCircleClasp_last :
    (D.insertCircleClasp p o b).crossingSign (Fin.last (n + 1)) =
      -(D.insertCircleClasp p o b).crossingSign (Fin.last n).castSucc := by
  simp only [crossingSign_def, toPDCode_insertCircleClasp, crossing_apply,
    crossingSlotEquiv_succ_last, crossingSlotEquiv_succ_castSucc,
    PDCode.insertCircleClasp_crossing_castSucc_last, PDCode.insertCircleClasp_crossing_last,
    orientation_insertCircleClasp_first, orientation_insertCircleClasp_second,
    insertCircleClasp_overPair_last, insertCircleClasp_overPair_castSucc_last]
  cases h : D.orientation p <;> cases o <;> cases b <;> simp

/-- The circle-and-arc clasp preserves writhe. -/
@[simp] theorem writhe_insertCircleClasp : (D.insertCircleClasp p o b).writhe = D.writhe := by
  rw [writhe_def, writhe_def, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    crossingSign_insertCircleClasp_last]
  simp

/-- Reflection exchanges the over-strand and retains the new circle's direction. -/
@[simp] theorem mirror_insertCircleClasp :
    (D.insertCircleClasp p o b).mirror = D.mirror.insertCircleClasp p o (!b) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | s
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | s <;> simp [insertCircleClasp]
    · simp [insertCircleClasp]
  · simp

/-- Reversing all components also reverses the new circle's direction. -/
@[simp] theorem reverse_insertCircleClasp :
    (D.insertCircleClasp p o b).reverse = D.reverse.insertCircleClasp p (!o) b := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv (n + 1)).surjective x
    rcases x with x | s
    · obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      rcases x with x | s
      · simp [insertCircleClasp]
      · fin_cases s <;> simp [insertCircleClasp]
    · fin_cases s <;> simp [insertCircleClasp]
  · simp

/-- The writhe-normalized bracket is invariant under the circle-and-arc move. -/
@[simp] theorem normalizedKauffmanBracket_insertCircleClasp {R : Type*} [CommRing R] (a : Rˣ) :
    (D.insertCircleClasp p o b).normalizedKauffmanBracket a =
      (D.adjoinCircle o).normalizedKauffmanBracket a := by
  rw [normalizedKauffmanBracket_def, normalizedKauffmanBracket_def]
  simp

end TauCeti.OrientedPDCode
