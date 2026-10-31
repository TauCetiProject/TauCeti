/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Closure properties of analytic sets

Mathlib's analytic sets (`MeasureTheory.AnalyticSet`) are closed under countable unions and
intersections, continuous images and continuous preimages from Polish spaces. This file adds the
finite and relational closure properties used to manipulate analytic relations and analytic
equivalence relations: binary intersections and unions, intersections with Borel sets, products,
off-diagonals, projections, and images and preimages of an analytic set under an analytic
relation `R : SetRel α β`. In a Hausdorff space the last of these show that the saturation
`Quotient.mk E ⁻¹' (Quotient.mk E '' A)` of an analytic set `A` under an equivalence relation `E`
with analytic graph is analytic, and so is the neighbourhood
`{x | ∃ y ∈ A, (x, y) ∈ G ∨ (y, x) ∈ G}` of `A` under an analytic relation `G`, which is
`(G ∪ G.inv).preimage A` and is analytic by `(hG.union hG.relInv).relPreimage hA`. Combined with
Lusin separation (`MeasureTheory.AnalyticSet.measurablySeparable`), these are the inputs of
separation arguments that alternate between Borel separators and their saturations or
neighbourhoods.

Binary intersections are proved in a Hausdorff ambient space, as Mathlib's
`MeasureTheory.AnalyticSet.iInter` is. Intersection with a Borel set needs no separation axiom: an
analytic set is the continuous image of a Polish space, and the preimage of a Borel set there is
Borel, hence analytic.

## Main results

* `MeasureTheory.AnalyticSet.inter`, `MeasureTheory.AnalyticSet.union`: binary intersections (in a
  Hausdorff space) and unions of analytic sets are analytic.
* `MeasureTheory.AnalyticSet.inter_measurableSet`: the intersection of an analytic set with a Borel
  set is analytic.
* `MeasureTheory.AnalyticSet.prod`, `MeasureTheory.AnalyticSet.offDiag`: products of analytic
  sets, and off-diagonals of analytic sets in a Hausdorff space, are analytic.
* `MeasureTheory.AnalyticSet.relImage`, `MeasureTheory.AnalyticSet.relPreimage`: the image and
  preimage of an analytic set under an analytic relation are analytic.
* `MeasureTheory.AnalyticSet.relImage_measurableSet`,
  `MeasureTheory.AnalyticSet.relPreimage_measurableSet`: the image and preimage of a Borel set
  under an analytic relation are analytic, with no separation axiom.
* `MeasureTheory.AnalyticSet.preimage_image_quotientMk`: the saturation of an analytic set under an
  equivalence relation with analytic graph is analytic.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Proposition 14.4 (closure properties of analytic sets).
* `inter`, `inter_measurableSet`, `prod` and `offDiag` are adapted from
  `InfinitaryLogic/Descriptive/AnalyticClosure.lean` in `cameronfreer/infinitary-logic`
  (Apache-2.0); the proofs of `inter` and `prod` follow it, and `inter_measurableSet` is stated
  there for Polish spaces only.
-/

public section

open Set

namespace MeasureTheory

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The intersection of two analytic sets in a Hausdorff space is analytic. -/
protected theorem AnalyticSet.inter [T2Space α] {s t : Set α} (hs : AnalyticSet s)
    (ht : AnalyticSet t) : AnalyticSet (s ∩ t) := by
  rw [inter_eq_iInter]
  exact AnalyticSet.iInter (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- The union of two analytic sets is analytic. -/
protected theorem AnalyticSet.union {s t : Set α} (hs : AnalyticSet s) (ht : AnalyticSet t) :
    AnalyticSet (s ∪ t) := by
  rw [union_eq_iUnion]
  exact AnalyticSet.iUnion (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- The intersection of an analytic set with a Borel set is analytic, in any topological space
with its Borel σ-algebra. -/
theorem AnalyticSet.inter_measurableSet [MeasurableSpace α] [BorelSpace α]
    {s t : Set α} (hs : AnalyticSet s) (ht : MeasurableSet t) : AnalyticSet (s ∩ t) := by
  obtain ⟨γ, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hs
  borelize γ
  rw [← image_preimage_eq_range_inter]
  exact (hf.measurable ht).analyticSet.image_of_continuous hf

/-- The product of two analytic sets is analytic. -/
protected theorem AnalyticSet.prod {s : Set α} {t : Set β} (hs : AnalyticSet s)
    (ht : AnalyticSet t) : AnalyticSet (s ×ˢ t) := by
  obtain ⟨γ, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hs
  obtain ⟨δ, _, _, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 ht
  rw [← range_prodMap]
  exact analyticSet_range_of_polishSpace (hf.prodMap hg)

/-- The set of pairs of distinct points of an analytic set in a Hausdorff space is analytic. -/
protected theorem AnalyticSet.offDiag [T2Space α] {s : Set α} (hs : AnalyticSet s) :
    AnalyticSet s.offDiag := by
  borelize (α × α)
  rw [offDiag_eq_sep_prod]
  exact (hs.prod hs).inter_measurableSet isClosed_diagonal.isOpen_compl.measurableSet

/-- The first projection of an analytic subset of a product is analytic. -/
theorem AnalyticSet.image_fst {s : Set (α × β)} (hs : AnalyticSet s) :
    AnalyticSet (Prod.fst '' s) :=
  hs.image_of_continuous continuous_fst

/-- The second projection of an analytic subset of a product is analytic. -/
theorem AnalyticSet.image_snd {s : Set (α × β)} (hs : AnalyticSet s) :
    AnalyticSet (Prod.snd '' s) :=
  hs.image_of_continuous continuous_snd

/-- The inverse of an analytic relation is analytic. -/
theorem AnalyticSet.relInv {R : SetRel α β} (hR : AnalyticSet R) : AnalyticSet R.inv := by
  rw [SetRel.inv, ← image_swap_eq_preimage_swap]
  exact hR.image_of_continuous continuous_swap

/-- The image of an analytic set under an analytic relation is analytic, when the domain is
Hausdorff. -/
theorem AnalyticSet.relImage [T2Space α] {R : SetRel α β} (hR : AnalyticSet R) {s : Set α}
    (hs : AnalyticSet s) : AnalyticSet (R.image s) := by
  obtain ⟨γ, _, _, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hR
  have : SetRel.image (range g) s = (fun c ↦ (g c).2) '' ((fun c ↦ (g c).1) ⁻¹' s) := by
    ext b
    simp only [SetRel.mem_image, mem_range, mem_image, mem_preimage]
    constructor
    · rintro ⟨a, ha, c, hc⟩
      exact ⟨c, by simpa [hc] using ha, by simp [hc]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨(g c).1, hc, c, rfl⟩
  rw [this]
  exact (hs.preimage hg.fst).image_of_continuous hg.snd

/-- The preimage of an analytic set under an analytic relation is analytic, when the codomain is
Hausdorff. -/
theorem AnalyticSet.relPreimage [T2Space β] {R : SetRel α β} (hR : AnalyticSet R) {t : Set β}
    (ht : AnalyticSet t) : AnalyticSet (R.preimage t) := by
  rw [← SetRel.image_inv]
  exact hR.relInv.relImage ht

/-- The preimage of a Borel set under an analytic relation is analytic. No separation axiom is
needed: the preimage is the first projection of the intersection of the relation with a Borel
set. -/
theorem AnalyticSet.relPreimage_measurableSet [MeasurableSpace β] [BorelSpace β] {R : SetRel α β}
    (hR : AnalyticSet R) {t : Set β} (ht : MeasurableSet t) : AnalyticSet (R.preimage t) := by
  borelize (α × β)
  have : R.preimage t = Prod.fst '' (R ∩ Prod.snd ⁻¹' t) := by
    ext a
    simp [and_comm]
  rw [this]
  exact (hR.inter_measurableSet (continuous_snd.measurable ht)).image_fst

/-- The image of a Borel set under an analytic relation is analytic. -/
theorem AnalyticSet.relImage_measurableSet [MeasurableSpace α] [BorelSpace α] {R : SetRel α β}
    (hR : AnalyticSet R) {s : Set α} (hs : MeasurableSet s) : AnalyticSet (R.image s) := by
  rw [← SetRel.preimage_inv]
  exact hR.relInv.relPreimage_measurableSet hs

/-- The saturation of an analytic set under an equivalence relation with analytic graph, in a
Hausdorff space, is analytic. -/
theorem AnalyticSet.preimage_image_quotientMk [T2Space α] {E : Setoid α}
    (hE : AnalyticSet {p : α × α | E p.1 p.2}) {s : Set α} (hs : AnalyticSet s) :
    AnalyticSet (Quotient.mk E ⁻¹' (Quotient.mk E '' s)) := by
  have : Quotient.mk E ⁻¹' (Quotient.mk E '' s) = SetRel.preimage {p : α × α | E p.1 p.2} s := by
    ext x
    simp only [mem_preimage, mem_image, Quotient.eq, SetRel.mem_preimage, mem_ofPred_eq]
    exact exists_congr fun y ↦ and_congr_right fun _ ↦ ⟨E.symm, E.symm⟩
  rw [this]
  exact hE.relPreimage hs

end MeasureTheory
