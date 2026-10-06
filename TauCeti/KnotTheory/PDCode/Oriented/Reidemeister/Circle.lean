/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.Circle

/-!
# An oriented Reidemeister kink on a crossing-free circle

`OrientedPDCode.adjoinKink D o b` is the oriented version of `PDCode.adjoinKink`.
The orientation `o` selects the direction of its isolated component and `b` selects its
over-strand. The first Reidemeister move relates this diagram to `D.adjoinCircle o`.

The new crossing has sign `+1` for `b = true` and `-1` for `b = false`, independently of
`o`. Its writhe correction cancels the Kauffman bracket factor. Thus adjoining an oriented
kink and adjoining a crossing-free circle give the same normalized bracket, even when `D`
is empty. The resulting Jones polynomial equality is in `TauCeti.KnotTheory.PDCode.Jones`.
The construction commutes with reflection and with reversing all component orientations.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapters 1 and 3 (oriented Reidemeister moves and the Jones polynomial).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

namespace TauCeti
namespace OrientedPDCode

open PDCode

variable {n : ℕ}

/-- Adjoin an oriented isolated kink. Its slots `1` and `2` have direction `o`, and slots
`0` and `3` have the opposite direction. Smoothing away the kink leaves the newly adjoined
circle in `D.adjoinCircle o`. -/
def adjoinKink (D : OrientedPDCode n) (o b : Bool) : OrientedPDCode (n + 1) where
  toPDCode := D.toPDCode.adjoinKink b
  orientation x := Sum.elim D.orientation (fun s => ![!o, o, o, !o] s)
    ((halfEdgeSuccEquiv n).symm x)
  orientation_edgePair := by
    intro x
    obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    · simp
    · rw [adjoinKink_edgePair_inr]
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, slotSmoothing_true]
      fin_cases s <;> cases o <;> decide
  orientation_oppositeCrossingSlot := by
    intro i s
    induction i using Fin.lastCases with
    | last =>
      simp only [← crossing_apply, adjoinKink_crossing_last, Equiv.symm_apply_apply,
        Sum.elim_inr, oppositeCrossingSlot_apply]
      fin_cases s <;> cases o <;> decide
    | cast i => simp
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

/-- Forgetting orientation gives the isolated unoriented kink. -/
@[simp] theorem toPDCode_adjoinKink (D : OrientedPDCode n) (o b : Bool) :
    (D.adjoinKink o b).toPDCode = D.toPDCode.adjoinKink b := (rfl)

/-- The old half-edges keep their orientations. -/
@[simp] theorem orientation_adjoinKink_inl (D : OrientedPDCode n) (o b : Bool)
    (x : Fin (4 * n)) :
    (D.adjoinKink o b).orientation (halfEdgeSuccEquiv n (.inl x)) = D.orientation x := by
  simp [adjoinKink]

/-- The directions at the four new slots. -/
@[simp] theorem orientation_adjoinKink_inr (D : OrientedPDCode n) (o b : Bool) (s : Fin 4) :
    (D.adjoinKink o b).orientation (halfEdgeSuccEquiv n (.inr s)) = ![!o, o, o, !o] s := by
  simp [adjoinKink]

/-- The crossing-free components of the surrounding diagram are unchanged. -/
@[simp] theorem crossinglessComponents_adjoinKink (D : OrientedPDCode n) (o b : Bool) :
    (D.adjoinKink o b).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Every old crossing keeps its sign. -/
@[simp] theorem crossingSign_adjoinKink_castSucc (D : OrientedPDCode n) (o b : Bool)
    (i : Fin n) :
    (D.adjoinKink o b).crossingSign i.castSucc = D.crossingSign i := by
  simp [crossingSign_def]

/-- The isolated kink has positive sign exactly when its over-pair indicator is true. -/
@[simp] theorem crossingSign_adjoinKink_last (D : OrientedPDCode n) (o b : Bool) :
    (D.adjoinKink o b).crossingSign (Fin.last n) = if b then 1 else -1 := by
  cases o <;> cases b <;> simp [crossingSign_def]

/-- The isolated kink changes the writhe by its crossing sign. -/
@[simp] theorem writhe_adjoinKink (D : OrientedPDCode n) (o b : Bool) :
    (D.adjoinKink o b).writhe = D.writhe + if b then 1 else -1 := by
  rw [writhe_def, writhe_def, Fin.sum_univ_castSucc]
  simp

/-- Removing the kink from an isolated oriented component leaves the normalized bracket
unchanged. No nonemptiness assumption on the surrounding diagram is needed. -/
@[simp] theorem normalizedKauffmanBracket_adjoinKink {R : Type*} [CommRing R]
    (D : OrientedPDCode n) (o b : Bool) (a : Rˣ) :
    (D.adjoinKink o b).normalizedKauffmanBracket a =
      (D.adjoinCircle o).normalizedKauffmanBracket a := by
  have hfactor : -(((bif b then a else a⁻¹ : Rˣ) : R) ^ 3) =
      (((-a ^ 3) ^ (if b then 1 else -1 : ℤ) : Rˣ) : R) := by
    cases b <;> simp
  rw [normalizedKauffmanBracket_def, normalizedKauffmanBracket_def, writhe_adjoinKink,
    writhe_adjoinCircle, toPDCode_adjoinKink, toPDCode_adjoinCircle,
    kauffmanBracket_adjoinKink, hfactor, ← mul_assoc, ← Units.val_mul, ← zpow_add]
  have hexponent : -(D.writhe + if b then 1 else -1) +
      (if b then 1 else -1 : ℤ) = -D.writhe := by omega
  rw [hexponent]

/-- Reflection reverses the crossing sign without changing the component direction. -/
@[simp] theorem mirror_adjoinKink (D : OrientedPDCode n) (o b : Bool) :
    (D.adjoinKink o b).mirror = D.mirror.adjoinKink o (!b) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x <;> simp
  · simp

/-- Reversing all component directions reverses the new kink as well. -/
@[simp] theorem reverse_adjoinKink (D : OrientedPDCode n) (o b : Bool) :
    (D.adjoinKink o b).reverse = D.reverse.adjoinKink (!o) b := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · simp
    · apply Subtype.ext
      simp [adjoinKink_edgePair_val]
    · simp
    · simp
  · funext x
    obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    · simp
    · fin_cases s <;> simp
  · simp

end OrientedPDCode
end TauCeti
