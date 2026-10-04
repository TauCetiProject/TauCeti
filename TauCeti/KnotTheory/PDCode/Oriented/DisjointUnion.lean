/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.DisjointUnion.Basic

/-!
# Disjoint unions of oriented diagrams

Disjoint union retains each component's direction, including the directions on crossing-free
circles. Crossing signs are unchanged, and writhe is additive. Consequently the writhe-normalized
Kauffman bracket has the same disjoint-union formula as the unoriented bracket. This is the
formula used to transport an invariant local replacement of an isolated diagram into an arbitrary
surrounding diagram.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3,
  Theorem 3.5 (the writhe normalization).
-/

public section

namespace TauCeti.OrientedPDCode

open PDCode TemperleyLieb

variable {n m : ℕ}

/-- Disjoint union retains the direction of each component of the two diagrams. -/
def disjointUnion (D : OrientedPDCode n) (E : OrientedPDCode m) : OrientedPDCode (n + m) where
  toPDCode := D.toPDCode.disjointUnion E.toPDCode
  orientation := Sum.elim D.orientation E.orientation ∘ (disjointUnionHalfEdgeEquiv n m).symm
  orientation_edgePair := by
    intro x
    obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
    rcases x with x | x <;> simp [disjointUnion_edgePair_val]
  orientation_oppositeCrossingSlot := by
    intro i slot
    induction i using Fin.addCases with
    | left i =>
      simp only [← crossing_apply, crossing_disjointUnion_castAdd, Function.comp_apply,
        Equiv.symm_apply_apply, Sum.elim_inl]
      simpa only [crossing_apply] using D.orientation_oppositeCrossingSlot i slot
    | right i =>
      simp only [← crossing_apply, crossing_disjointUnion_natAdd, Function.comp_apply,
        Equiv.symm_apply_apply, Sum.elim_inr]
      simpa only [crossing_apply] using E.orientation_oppositeCrossingSlot i slot
  crossinglessComponents := D.crossinglessComponents + E.crossinglessComponents
  crossinglessComponents_card := by simp

variable (D : OrientedPDCode n) (E : OrientedPDCode m)

/-- Forgetting orientations commutes with disjoint union. -/
@[simp]
theorem toPDCode_disjointUnion :
    (D.disjointUnion E).toPDCode = D.toPDCode.disjointUnion E.toPDCode := (rfl)

/-- The first diagram's half-edges retain their directions. -/
@[simp]
theorem orientation_disjointUnion_inl (x : Fin (4 * n)) :
    (D.disjointUnion E).orientation (disjointUnionHalfEdgeEquiv n m (.inl x)) =
      D.orientation x := by
  simp [disjointUnion]

/-- The second diagram's half-edges retain their directions. -/
@[simp]
theorem orientation_disjointUnion_inr (x : Fin (4 * m)) :
    (D.disjointUnion E).orientation (disjointUnionHalfEdgeEquiv n m (.inr x)) =
      E.orientation x := by
  simp [disjointUnion]

/-- The crossing-free circles and their directions are concatenated as multisets. -/
@[simp]
theorem crossinglessComponents_disjointUnion :
    (D.disjointUnion E).crossinglessComponents =
      D.crossinglessComponents + E.crossinglessComponents := (rfl)

/-- Reflection commutes with oriented disjoint union. -/
@[simp]
theorem mirror_disjointUnion :
    (D.disjointUnion E).mirror = D.mirror.disjointUnion E.mirror := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
    rcases x with x | x <;> simp
  · simp

/-- Reversing every component commutes with disjoint union. -/
@[simp]
theorem reverse_disjointUnion :
    (D.disjointUnion E).reverse = D.reverse.disjointUnion E.reverse := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
    rcases x with x | x <;> simp
  · simp

/-- Every crossing of the first diagram retains its sign. -/
@[simp]
theorem crossingSign_disjointUnion_castAdd (i : Fin n) :
    (D.disjointUnion E).crossingSign (Fin.castAdd m i) = D.crossingSign i := by
  simp [crossingSign_def, toPDCode_disjointUnion]

/-- Every crossing of the second diagram retains its sign. -/
@[simp]
theorem crossingSign_disjointUnion_natAdd (i : Fin m) :
    (D.disjointUnion E).crossingSign (Fin.natAdd n i) = E.crossingSign i := by
  simp [crossingSign_def, toPDCode_disjointUnion]

/-- Writhe is additive under disjoint union. -/
@[simp]
theorem writhe_disjointUnion : (D.disjointUnion E).writhe = D.writhe + E.writhe := by
  simp [writhe_def, Fin.sum_univ_add]

/-- The normalized bracket of two nonempty disjoint diagrams is the product of their normalized
brackets times the circle value. -/
@[simp]
theorem normalizedKauffmanBracket_disjointUnion {R : Type*} [CommRing R] (a : Rˣ)
    (hD : 0 < D.toPDCode.componentCount) (hE : 0 < E.toPDCode.componentCount) :
    (D.disjointUnion E).normalizedKauffmanBracket a =
      jonesDelta a * D.normalizedKauffmanBracket a * E.normalizedKauffmanBracket a := by
  simp only [normalizedKauffmanBracket_def, writhe_disjointUnion, toPDCode_disjointUnion,
    PDCode.kauffmanBracket_disjointUnion _ _ a hD hE, neg_add, zpow_add, Units.val_mul]
  ring

/-- An empty first summand leaves the other diagram's normalized bracket unchanged. -/
@[simp]
theorem normalizedKauffmanBracket_disjointUnion_of_componentCount_eq_zero_left
    {R : Type*} [CommRing R] (a : Rˣ) (hD : D.toPDCode.componentCount = 0) :
    (D.disjointUnion E).normalizedKauffmanBracket a = E.normalizedKauffmanBracket a := by
  have hn : n = 0 := by
    by_contra hn
    have := D.toPDCode.componentCount_pos hn
    omega
  subst n
  have hw : D.writhe = 0 := by simp [writhe_def]
  simp only [normalizedKauffmanBracket_def, writhe_disjointUnion, hw, zero_add,
    toPDCode_disjointUnion,
    PDCode.kauffmanBracket_disjointUnion_of_componentCount_eq_zero_left _ _ a hD]

/-- An empty second summand leaves the other diagram's normalized bracket unchanged. -/
@[simp]
theorem normalizedKauffmanBracket_disjointUnion_of_componentCount_eq_zero_right
    {R : Type*} [CommRing R] (a : Rˣ) (hE : E.toPDCode.componentCount = 0) :
    (D.disjointUnion E).normalizedKauffmanBracket a = D.normalizedKauffmanBracket a := by
  have hm : m = 0 := by
    by_contra hm
    have := E.toPDCode.componentCount_pos hm
    omega
  subst m
  have hw : E.writhe = 0 := by simp [writhe_def]
  simp only [normalizedKauffmanBracket_def, writhe_disjointUnion, hw, add_zero,
    toPDCode_disjointUnion,
    PDCode.kauffmanBracket_disjointUnion_of_componentCount_eq_zero_right _ _ a hE]

end TauCeti.OrientedPDCode
