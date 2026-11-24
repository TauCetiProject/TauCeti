/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.DisjointUnion.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Component

/-!
# Disjoint unions of oriented diagrams

Disjoint union retains each component's direction, including the directions on crossing-free
circles. Crossing signs are unchanged, and writhe is additive. Consequently the writhe-normalized
Kauffman bracket has the same disjoint-union formula as the unoriented bracket. This is the
formula used to transport an invariant local replacement of an isolated diagram into an arbitrary
surrounding diagram.

`OrientedPDCode.disjointUnionComponentEquiv` decomposes the labelled components of a disjoint union
into those of its two summands, keeping half-edge representatives in each block and numbering the
first summand's crossing-free circles before those of the second.

## Main definitions

* `TauCeti.OrientedPDCode.disjointUnion`: disjoint union of oriented PD-codes.
* `TauCeti.OrientedPDCode.disjointUnionCrossingComponentEquiv`: decomposition of crossing-bearing
  components of a disjoint union.
* `TauCeti.OrientedPDCode.disjointUnionComponentEquiv`: decomposition of all labelled components of
  a disjoint union.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3,
  Theorem 3.5 (the writhe normalization).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3 (oriented component traversal).
-/

public section

namespace TauCeti.OrientedPDCode

open Equiv Equiv.Perm PDCode TemperleyLieb

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
  card_crossinglessComponents := by simp

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

/-! ### Component decomposition -/

/-- Outgoing half-edges of a disjoint union split into outgoing half-edges of the two summands. -/
def disjointUnionOutgoingEquiv :
    {h : Fin (4 * (n + m)) // (D.disjointUnion E).orientation h = true} ≃
      {h : Fin (4 * n) // D.orientation h = true} ⊕
        {h : Fin (4 * m) // E.orientation h = true} :=
  ((disjointUnionHalfEdgeEquiv n m).symm.subtypeEquiv
    (q := fun z ↦ Sum.elim D.orientation E.orientation z = true) fun x ↦ by
      obtain ⟨z, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
      rcases z with z | z <;> simp).trans
    Equiv.subtypeSum

/-- An outgoing half-edge from the first summand maps to the left outgoing summand. -/
@[simp]
theorem disjointUnionOutgoingEquiv_inl (x : Fin (4 * n))
    (hx : (D.disjointUnion E).orientation (disjointUnionHalfEdgeEquiv n m (.inl x)) = true) :
    D.disjointUnionOutgoingEquiv E ⟨disjointUnionHalfEdgeEquiv n m (.inl x), hx⟩ =
      .inl ⟨x, by simpa using hx⟩ := by
  simp [disjointUnionOutgoingEquiv, Equiv.subtypeEquiv, Equiv.subtypeSum]

/-- An outgoing half-edge from the second summand maps to the right outgoing summand. -/
@[simp]
theorem disjointUnionOutgoingEquiv_inr (y : Fin (4 * m))
    (hy : (D.disjointUnion E).orientation (disjointUnionHalfEdgeEquiv n m (.inr y)) = true) :
    D.disjointUnionOutgoingEquiv E ⟨disjointUnionHalfEdgeEquiv n m (.inr y), hy⟩ =
      .inr ⟨y, by simpa using hy⟩ := by
  simp [disjointUnionOutgoingEquiv, Equiv.subtypeEquiv, Equiv.subtypeSum]

/-- Including an outgoing half-edge of the first summand uses the left half-edge block. -/
@[simp]
theorem disjointUnionOutgoingEquiv_symm_inl (h : {h : Fin (4 * n) // D.orientation h = true}) :
    (D.disjointUnionOutgoingEquiv E).symm (.inl h) =
      ⟨disjointUnionHalfEdgeEquiv n m (.inl h.val), by simp [h.property]⟩ := by
  apply (D.disjointUnionOutgoingEquiv E).injective
  simp

/-- Including an outgoing half-edge of the second summand uses the right half-edge block. -/
@[simp]
theorem disjointUnionOutgoingEquiv_symm_inr (h : {h : Fin (4 * m) // E.orientation h = true}) :
    (D.disjointUnionOutgoingEquiv E).symm (.inr h) =
      ⟨disjointUnionHalfEdgeEquiv n m (.inr h.val), by simp [h.property]⟩ := by
  apply (D.disjointUnionOutgoingEquiv E).injective
  simp

/-- Outgoing component traversal on a disjoint union acts separately on the two summands. -/
theorem componentPermOutgoing_disjointUnion :
    (D.disjointUnion E).componentPermOutgoing =
      (D.disjointUnionOutgoingEquiv E).symm.permCongr
        (Perm.sumCongr D.componentPermOutgoing E.componentPermOutgoing) := by
  ext h
  obtain ⟨z, rfl⟩ := (D.disjointUnionOutgoingEquiv E).symm.surjective h
  rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rcases z with z | z <;>
    simp [disjointUnionOutgoingEquiv_symm_inl, disjointUnionOutgoingEquiv_symm_inr,
      PDCode.componentPerm_disjointUnion, Equiv.permCongr_apply]

noncomputable section

/-- Crossing-bearing components of a disjoint union split into those of the two summands. -/
def disjointUnionCrossingComponentEquiv :
    (D.disjointUnion E).CrossingComponent ≃ D.CrossingComponent ⊕ E.CrossingComponent :=
  ((D.disjointUnionOutgoingEquiv E).sameCycleQuotientCongr (by
    ext z
    simp [componentPermOutgoing_disjointUnion])).trans
    (sameCycleQuotientSumCongrEquiv D.componentPermOutgoing E.componentPermOutgoing)

/-- Including a crossing component of `D` acts on half-edge representatives by left inclusion. -/
@[simp]
theorem disjointUnionCrossingComponentEquiv_symm_inl_halfEdge (x : Fin (4 * n)) :
    (D.disjointUnionCrossingComponentEquiv E).symm (.inl (D.crossingComponentOfHalfEdge x)) =
      (D.disjointUnion E).crossingComponentOfHalfEdge
        (disjointUnionHalfEdgeEquiv n m (.inl x)) :=
  D.apply_crossingComponentOfHalfEdge
    (fun c ↦ (D.disjointUnionCrossingComponentEquiv E).symm (.inl c))
    (fun x ↦ (D.disjointUnion E).crossingComponentOfHalfEdge
      (disjointUnionHalfEdgeEquiv n m (.inl x)))
    (fun x ↦ by
      have hpair : (D.disjointUnion E).edgePair.val (disjointUnionHalfEdgeEquiv n m (.inl x)) =
          disjointUnionHalfEdgeEquiv n m (.inl (D.edgePair.val x)) := by
        simp [PDCode.disjointUnion_edgePair_val, Equiv.permCongr_apply]
      rw [← hpair, crossingComponentOfHalfEdge_edgePair])
    (fun h ↦ by
      rw [crossingComponentOfHalfEdge_of_outgoing (D.disjointUnion E) _ (by simp [h.property])]
      simp [disjointUnionCrossingComponentEquiv])
    x

/-- Including a crossing component of `E` acts on half-edge representatives by right inclusion. -/
@[simp]
theorem disjointUnionCrossingComponentEquiv_symm_inr_halfEdge (y : Fin (4 * m)) :
    (D.disjointUnionCrossingComponentEquiv E).symm (.inr (E.crossingComponentOfHalfEdge y)) =
      (D.disjointUnion E).crossingComponentOfHalfEdge
        (disjointUnionHalfEdgeEquiv n m (.inr y)) :=
  E.apply_crossingComponentOfHalfEdge
    (fun c ↦ (D.disjointUnionCrossingComponentEquiv E).symm (.inr c))
    (fun y ↦ (D.disjointUnion E).crossingComponentOfHalfEdge
      (disjointUnionHalfEdgeEquiv n m (.inr y)))
    (fun y ↦ by
      have hpair : (D.disjointUnion E).edgePair.val (disjointUnionHalfEdgeEquiv n m (.inr y)) =
          disjointUnionHalfEdgeEquiv n m (.inr (E.edgePair.val y)) := by
        simp [PDCode.disjointUnion_edgePair_val, Equiv.permCongr_apply]
      rw [← hpair, crossingComponentOfHalfEdge_edgePair])
    (fun h ↦ by
      rw [crossingComponentOfHalfEdge_of_outgoing (D.disjointUnion E) _ (by simp [h.property])]
      simp [disjointUnionCrossingComponentEquiv])
    y

/-- A half-edge in the first block represents the corresponding crossing component of `D`. -/
@[simp]
theorem disjointUnionCrossingComponentEquiv_halfEdge_inl (x : Fin (4 * n)) :
    D.disjointUnionCrossingComponentEquiv E
        ((D.disjointUnion E).crossingComponentOfHalfEdge
          (disjointUnionHalfEdgeEquiv n m (.inl x))) =
      .inl (D.crossingComponentOfHalfEdge x) := by
  apply (D.disjointUnionCrossingComponentEquiv E).symm.injective
  simp

/-- A half-edge in the second block represents the corresponding crossing component of `E`. -/
@[simp]
theorem disjointUnionCrossingComponentEquiv_halfEdge_inr (y : Fin (4 * m)) :
    D.disjointUnionCrossingComponentEquiv E
        ((D.disjointUnion E).crossingComponentOfHalfEdge
          (disjointUnionHalfEdgeEquiv n m (.inr y))) =
      .inr (E.crossingComponentOfHalfEdge y) := by
  apply (D.disjointUnionCrossingComponentEquiv E).symm.injective
  simp

/-- The labelled components of a disjoint union decompose into those of the two summands.
Crossing-free circles of `D` occupy the first block of labels, followed by those of `E`. -/
def disjointUnionComponentEquiv :
    (D.disjointUnion E).Component ≃ D.Component ⊕ E.Component :=
  ((D.disjointUnionCrossingComponentEquiv E).sumCongr
    ((finCongr (by simp)).trans finSumFinEquiv.symm)).trans
    (Equiv.sumSumSumComm _ _ _ _)

/-- Decomposition sends a half-edge in the first summand to its component in `D`. -/
@[simp]
theorem disjointUnionComponentEquiv_inl_halfEdge_inl (x : Fin (4 * n)) :
    D.disjointUnionComponentEquiv E
        (.inl ((D.disjointUnion E).crossingComponentOfHalfEdge
          (disjointUnionHalfEdgeEquiv n m (.inl x)))) =
      .inl (.inl (D.crossingComponentOfHalfEdge x)) := by
  simp [disjointUnionComponentEquiv]

/-- Decomposition sends a half-edge in the second summand to its component in `E`. -/
@[simp]
theorem disjointUnionComponentEquiv_inl_halfEdge_inr (y : Fin (4 * m)) :
    D.disjointUnionComponentEquiv E
        (.inl ((D.disjointUnion E).crossingComponentOfHalfEdge
          (disjointUnionHalfEdgeEquiv n m (.inr y)))) =
      .inr (.inl (E.crossingComponentOfHalfEdge y)) := by
  simp [disjointUnionComponentEquiv]

/-- Decomposition sends an outgoing representative of `D` to its component in `D`. -/
@[simp]
theorem disjointUnionComponentEquiv_componentOfOutgoing_inl (x : Fin (4 * n))
    (hx : (D.disjointUnion E).orientation (disjointUnionHalfEdgeEquiv n m (.inl x)) = true) :
    D.disjointUnionComponentEquiv E
        ((D.disjointUnion E).componentOfOutgoing
          ⟨disjointUnionHalfEdgeEquiv n m (.inl x), hx⟩) =
      .inl (D.componentOfOutgoing ⟨x, by simpa using hx⟩) := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.disjointUnionComponentEquiv_inl_halfEdge_inl E x

/-- Decomposition sends an outgoing representative of `E` to its component in `E`. -/
@[simp]
theorem disjointUnionComponentEquiv_componentOfOutgoing_inr (y : Fin (4 * m))
    (hy : (D.disjointUnion E).orientation (disjointUnionHalfEdgeEquiv n m (.inr y)) = true) :
    D.disjointUnionComponentEquiv E
        ((D.disjointUnion E).componentOfOutgoing
          ⟨disjointUnionHalfEdgeEquiv n m (.inr y), hy⟩) =
      .inr (E.componentOfOutgoing ⟨y, by simpa using hy⟩) := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.disjointUnionComponentEquiv_inl_halfEdge_inr E y

/-- Including a crossing component of `D` carries half-edge representatives by left inclusion. -/
@[simp]
theorem disjointUnionComponentEquiv_symm_inl_halfEdge (x : Fin (4 * n)) :
    (D.disjointUnionComponentEquiv E).symm (.inl (.inl (D.crossingComponentOfHalfEdge x))) =
      .inl ((D.disjointUnion E).crossingComponentOfHalfEdge
        (disjointUnionHalfEdgeEquiv n m (.inl x))) := by
  apply (D.disjointUnionComponentEquiv E).injective
  simp

/-- Including a crossing component of `E` carries half-edge representatives by right inclusion. -/
@[simp]
theorem disjointUnionComponentEquiv_symm_inr_halfEdge (y : Fin (4 * m)) :
    (D.disjointUnionComponentEquiv E).symm (.inr (.inl (E.crossingComponentOfHalfEdge y))) =
      .inl ((D.disjointUnion E).crossingComponentOfHalfEdge
        (disjointUnionHalfEdgeEquiv n m (.inr y))) := by
  apply (D.disjointUnionComponentEquiv E).injective
  simp

/-- Including an outgoing representative of `D` uses the left half-edge block. -/
@[simp]
theorem disjointUnionComponentEquiv_symm_inl_componentOfOutgoing
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    (D.disjointUnionComponentEquiv E).symm (.inl (D.componentOfOutgoing h)) =
      (D.disjointUnion E).componentOfOutgoing
        ⟨disjointUnionHalfEdgeEquiv n m (.inl h.val), by simp [h.property]⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.disjointUnionComponentEquiv_symm_inl_halfEdge E h.val

/-- Including an outgoing representative of `E` uses the right half-edge block. -/
@[simp]
theorem disjointUnionComponentEquiv_symm_inr_componentOfOutgoing
    (h : {h : Fin (4 * m) // E.orientation h = true}) :
    (D.disjointUnionComponentEquiv E).symm (.inr (E.componentOfOutgoing h)) =
      (D.disjointUnion E).componentOfOutgoing
        ⟨disjointUnionHalfEdgeEquiv n m (.inr h.val), by simp [h.property]⟩ := by
  simpa only [← inl_crossingComponentOfHalfEdge] using
    D.disjointUnionComponentEquiv_symm_inr_halfEdge E h.val

/-- Crossing-free circles of `D` occupy the initial block of crossing-free labels. -/
@[simp]
theorem disjointUnionComponentEquiv_symm_inl_inr (i : Fin D.crossinglessComponentCount) :
    (D.disjointUnionComponentEquiv E).symm (.inl (.inr i)) =
      .inr (Fin.cast (by simp) (Fin.castAdd E.crossinglessComponentCount i)) := by
  simp [disjointUnionComponentEquiv]

/-- Crossing-free circles of `E` occupy the final block of crossing-free labels. -/
@[simp]
theorem disjointUnionComponentEquiv_symm_inr_inr (j : Fin E.crossinglessComponentCount) :
    (D.disjointUnionComponentEquiv E).symm (.inr (.inr j)) =
      .inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount j)) := by
  simp [disjointUnionComponentEquiv]

/-- Decomposition recovers a crossing-free circle from the initial block of labels. -/
@[simp]
theorem disjointUnionComponentEquiv_inr_castAdd (i : Fin D.crossinglessComponentCount) :
    D.disjointUnionComponentEquiv E
        (.inr (Fin.cast (by simp) (Fin.castAdd E.crossinglessComponentCount i))) =
      .inl (.inr i) := by
  apply (D.disjointUnionComponentEquiv E).symm.injective
  simp

/-- Decomposition recovers a crossing-free circle from the final block of labels. -/
@[simp]
theorem disjointUnionComponentEquiv_inr_natAdd (j : Fin E.crossinglessComponentCount) :
    D.disjointUnionComponentEquiv E
        (.inr (Fin.cast (by simp) (Fin.natAdd D.crossinglessComponentCount j))) =
      .inr (.inr j) := by
  apply (D.disjointUnionComponentEquiv E).symm.injective
  simp

end

end TauCeti.OrientedPDCode
