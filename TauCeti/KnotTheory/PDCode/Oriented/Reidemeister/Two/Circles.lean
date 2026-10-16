/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.Two.Circles
public import TauCeti.KnotTheory.PDCode.Oriented.DisjointUnion

/-!
# Oriented Reidemeister clasps between two crossing-free circles

Orient the two components of the closed clasp independently. The signs of the two crossings
are opposite, and its writhe is zero. Adjoining this clasp to any oriented diagram has the
same normalized bracket and Jones polynomial as adjoining the two oriented crossing-free
circles. Both over-component choices and all four component orientations are included.

The slot orientations follow those of `OrientedPDCode.insertCircleClasp`, with both outside
arcs closed. Disjoint union transports the local polynomial identity into the surrounding
code without assuming that it is nonempty or planar.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 3,
  Lemma 3.3 and Theorem 3.5.
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

namespace TauCeti.OrientedPDCode

open PDCode

/-- Orient the two circles of the closed Reidemeister clasp by `o₁` and `o₂`.
At its first crossing, slots `2` and `3` have directions `o₁` and `o₂`, respectively.
The bit `b` selects its over-strand. -/
def twoCircleClasp (o₁ o₂ b : Bool) : OrientedPDCode 2 where
  toPDCode := PDCode.twoCircleClasp b
  orientation x :=
    let p := (crossingSlotEquiv 2).symm x
    (if p.1 = 0 then ![!o₁, !o₂, o₁, o₂] else ![!o₂, !o₁, o₂, o₁]) p.2
  orientation_edgePair := by
    intro x
    obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective x
    simp only [PDCode.twoCircleClasp_edgePair_val, Equiv.permCongr_apply,
      Equiv.symm_apply_apply, Equiv.prodCongr_apply]
    fin_cases i <;> fin_cases s <;> simp
  orientation_oppositeCrossingSlot := by
    intro i s
    simp only [PDCode.twoCircleClasp_halfEdge, Equiv.Perm.one_apply,
      Equiv.symm_apply_apply]
    fin_cases i <;> fin_cases s <;> simp [oppositeCrossingSlot_apply]
  crossinglessComponents := 0
  card_crossinglessComponents := by simp

/-- Forgetting orientation gives the closed unoriented clasp. -/
@[simp] theorem toPDCode_twoCircleClasp (o₁ o₂ b : Bool) :
    (twoCircleClasp o₁ o₂ b).toPDCode = PDCode.twoCircleClasp b := (rfl)

/-- The first component has direction `o₁`, and the second has direction `o₂`. -/
@[simp] theorem orientation_twoCircleClasp (o₁ o₂ b : Bool) (i : Fin 2) (s : Fin 4) :
    (twoCircleClasp o₁ o₂ b).orientation (crossingSlotEquiv 2 (i, s)) =
      (if i = 0 then ![!o₁, !o₂, o₁, o₂] else ![!o₂, !o₁, o₂, o₁]) s := by
  simp [twoCircleClasp]

/-- Neither component remains crossing-free. -/
@[simp] theorem crossinglessComponents_twoCircleClasp (o₁ o₂ b : Bool) :
    (twoCircleClasp o₁ o₂ b).crossinglessComponents = 0 := (rfl)

/-- The two crossings have opposite signs for every choice of component directions. -/
@[simp] theorem crossingSign_twoCircleClasp_one (o₁ o₂ b : Bool) :
    (twoCircleClasp o₁ o₂ b).crossingSign 1 = -(twoCircleClasp o₁ o₂ b).crossingSign 0 := by
  simp only [crossingSign_def, crossing_apply, toPDCode_twoCircleClasp,
    PDCode.twoCircleClasp_halfEdge, PDCode.twoCircleClasp_overPair, Equiv.Perm.one_apply,
    orientation_twoCircleClasp]
  cases o₁ <;> cases o₂ <;> cases b <;> simp

/-- The cancelling pair contributes zero writhe. -/
@[simp] theorem writhe_twoCircleClasp (o₁ o₂ b : Bool) : (twoCircleClasp o₁ o₂ b).writhe = 0 := by
  simp [writhe_def, Fin.sum_univ_two]

/-- Reflection exchanges the over-component without changing its direction. -/
@[simp] theorem mirror_twoCircleClasp (o₁ o₂ b : Bool) :
    (twoCircleClasp o₁ o₂ b).mirror = twoCircleClasp o₁ o₂ (!b) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective x
    simp only [mirror_orientation, orientation_twoCircleClasp]
  · simp

/-- Reversing all components flips the two specified circle directions. -/
@[simp] theorem reverse_twoCircleClasp (o₁ o₂ b : Bool) :
    (twoCircleClasp o₁ o₂ b).reverse = twoCircleClasp (!o₁) (!o₂) b := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective x
    fin_cases i <;> fin_cases s <;>
      simp only [reverse_orientation, orientation_twoCircleClasp]
    all_goals simp
  · simp

/-- Adjoin a cancelling clasp between two additional oriented circles in a disc disjoint
from `D`. Compare it with `(D.adjoinCircle o₁).adjoinCircle o₂`. -/
def adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) : OrientedPDCode (n + 2) :=
  D.disjointUnion (twoCircleClasp o₁ o₂ b)

/-- The oriented disjoint-union characterization of clasp adjunction. -/
theorem adjoinTwoCircleClasp_def {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    D.adjoinTwoCircleClasp o₁ o₂ b = D.disjointUnion (twoCircleClasp o₁ o₂ b) := (rfl)

/-- Forgetting directions gives the unoriented two-circle move. -/
@[simp] theorem toPDCode_adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).toPDCode = D.toPDCode.adjoinTwoCircleClasp b := by
  simp [adjoinTwoCircleClasp_def, PDCode.adjoinTwoCircleClasp_def]

/-- Every old crossing-free component retains its direction. -/
@[simp] theorem crossinglessComponents_adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).crossinglessComponents = D.crossinglessComponents := by
  simp [adjoinTwoCircleClasp_def]

/-- The two-circle move preserves writhe. -/
@[simp] theorem writhe_adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).writhe = D.writhe := by
  simp [adjoinTwoCircleClasp_def]

/-- Reflection swaps the over-component of the adjoined clasp. -/
@[simp] theorem mirror_adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).mirror = D.mirror.adjoinTwoCircleClasp o₁ o₂ (!b) := by
  simp [adjoinTwoCircleClasp_def]

/-- Reversal flips both adjoined component directions. -/
@[simp] theorem reverse_adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).reverse = D.reverse.adjoinTwoCircleClasp (!o₁) (!o₂) b := by
  simp [adjoinTwoCircleClasp_def]

/-- The normalized bracket is unchanged by the two-circle second Reidemeister move,
with no nonemptiness assumption on the surrounding diagram. -/
@[simp] theorem normalizedKauffmanBracket_adjoinTwoCircleClasp {n : ℕ} {R : Type*} [CommRing R]
    (D : OrientedPDCode n) (o₁ o₂ b : Bool) (a : Rˣ) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).normalizedKauffmanBracket a =
      ((D.adjoinCircle o₁).adjoinCircle o₂).normalizedKauffmanBracket a := by
  simp [normalizedKauffmanBracket_def]

end TauCeti.OrientedPDCode
