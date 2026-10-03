/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Counted
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Weight

/-!
# Removing common-initial-side contributions from the pentagon chain-map equation

A counted rectangle followed by a pentagon, sharing exactly their initial side column,
recuts to a counted pentagon followed by a rectangle. The recut is injective and preserves
the monomial weight. This file identifies the total contributions of these sources and
their partners and removes them from the two coefficient sums in the chain-map equation.

`GridDiagram.initialOverlapPartners` is precisely the image of
`GridDiagram.initialOverlapSources` under this recut. Its membership characterization uses
the recut relation on the underlying rectangles; it does not assert that every mixed-side
pentagon--rectangle decomposition belongs to the image. Requiring exactly one common side
excludes annular decompositions sharing both side columns.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  {x z : GridState n}

/-- The counted rectangle--pentagon decompositions with exactly one common side column,
initial for both domains. -/
noncomputable def initialOverlapSources (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectanglePentagonDecompositions C x z).filter fun D =>
    D.rectangle.left = D.pentagon.left ∧ D.toRectangleDecomposition.HasOneCommonSide

/-- Membership in the common-initial-side source family records counting and exactly one
common side column. -/
@[simp]
theorem mem_initialOverlapSources
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.initialOverlapSources C x z ↔
      D ∈ G.rectanglePentagonDecompositions C x z ∧
        D.rectangle.left = D.pentagon.left ∧ D.toRectangleDecomposition.HasOneCommonSide := by
  classical
  simp [initialOverlapSources]

private theorem initialOverlapSource_data
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.initialOverlapSources C x z) :
    D.rectangle.left = D.pentagon.left ∧
      D.toRectangleDecomposition.HasOneCommonSide ∧
        D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty := by
  obtain ⟨hcounted, hcommon, hone⟩ := (G.mem_initialOverlapSources C D).1 hD
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcounted
  exact ⟨hcommon, hone, ((G.mem_unblockedRectangles _).1 hr).1,
    ((G.mem_pentagons _).1 hP).1⟩

private theorem initialOverlapSource_underlying_isEmpty
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.initialOverlapSources C x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨_, _, hr, hP⟩ := G.initialOverlapSource_data C D hD
  constructor
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hr
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
      using hP

private noncomputable def initialOverlapPartner
    (D : {D // D ∈ G.initialOverlapSources C x z}) :
    GridPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutLeftEqLeft
    (G.initialOverlapSource_data C D.val D.property).1
    (G.initialOverlapSource_data C D.val D.property).2.1
    (G.initialOverlapSource_data C D.val D.property).2.2.1
    (G.initialOverlapSource_data C D.val D.property).2.2.2

private theorem initialOverlapPartner_isRecut
    (D : {D // D ∈ G.initialOverlapSources C x z}) :
    D.val.toRectangleDecomposition.IsRecut
      (G.initialOverlapPartner C D).toRectangleDecomposition := by
  unfold initialOverlapPartner
  exact D.val.isRecut_recutLeftEqLeft _ _ _ _

private theorem initialOverlapPartner_injective :
    Function.Injective (G.initialOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.initialOverlapPartner_isRecut C D
  have hE := G.initialOverlapPartner_isRecut C E
  rw [← h] at hE
  have honeD := (G.initialOverlapSource_data C D.val D.property).2.1
  have honeE := (G.initialOverlapSource_data C E.val E.property).2.1
  obtain ⟨hfD, hsD⟩ := G.initialOverlapSource_underlying_isEmpty C D.val D.property
  obtain ⟨hfE, hsE⟩ := G.initialOverlapSource_underlying_isEmpty C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

private theorem initialOverlapPartner_mem
    (D : {D // D ∈ G.initialOverlapSources C x z}) :
    G.initialOverlapPartner C D ∈ G.pentagonRectangleDecompositions C x z := by
  obtain ⟨hcounted, _, _⟩ := (G.mem_initialOverlapSources C D.val).1 D.property
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D.val).1 hcounted
  unfold initialOverlapPartner
  exact G.recutLeftEqLeft_mem_pentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_unblockedRectangles _).1 hr).2 ((G.mem_pentagons _).1 hP).2

/-- The pentagon--rectangle partners obtained by recutting the counted common-initial-side
sources. This family is the exact recut image of `initialOverlapSources`. -/
noncomputable def initialOverlapPartners (x z : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialOverlapSources C x z).attach.map
    ⟨G.initialOverlapPartner C, G.initialOverlapPartner_injective C⟩

/-- A pentagon--rectangle term is a partner exactly when its underlying rectangles are the
recut of a counted common-initial-side source. -/
@[simp]
theorem mem_initialOverlapPartners
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialOverlapPartners C x z ↔
      ∃ D ∈ G.initialOverlapSources C x z,
        D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [initialOverlapPartners, Finset.mem_map, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    have hone := (G.initialOverlapSource_data C D hD).2.1
    obtain ⟨hf, hs⟩ := G.initialOverlapSource_underlying_isEmpty C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
    exact (D.toRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
      (G.initialOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Each common-initial-side source belongs to the full rectangle--pentagon coefficient sum. -/
theorem initialOverlapSources_subset_rectanglePentagonDecompositions :
    G.initialOverlapSources C x z ⊆ G.rectanglePentagonDecompositions C x z := by
  intro D hD
  exact ((G.mem_initialOverlapSources C D).1 hD).1

/-- Each partner belongs to the full pentagon--rectangle coefficient sum. -/
theorem initialOverlapPartners_subset_pentagonRectangleDecompositions :
    G.initialOverlapPartners C x z ⊆ G.pentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [initialOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  exact G.initialOverlapPartner_mem C D

/-- Recutting identifies the total common-initial-side source contribution with the total
contribution of its pentagon--rectangle partners over any commutative coefficient semiring. -/
theorem sum_rectanglePentagonWeight_initialOverlapSources_eq_sum_pentagonRectangleWeight_partners
    (R : Type*) [CommSemiring R] (x z : GridState n) :
    ∑ D ∈ G.initialOverlapSources C x z, G.rectanglePentagonWeight C R D =
      ∑ E ∈ G.initialOverlapPartners C x z, G.pentagonRectangleWeight C R E := by
  classical
  have hweight (D : {D // D ∈ G.initialOverlapSources C x z}) :
      G.pentagonRectangleWeight C R (G.initialOverlapPartner C D) =
        G.rectanglePentagonWeight C R D.val := by
    unfold initialOverlapPartner
    exact G.pentagonRectangleWeight_recutLeftEqLeft C R D.val _ _ _ _
  rw [initialOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, hweight, Finset.sum_attach]

open scoped Classical in
/-- The two full pentagon chain-map coefficient sums agree exactly when their complements
after removing the common-initial-side sources and their recut partners agree. -/
theorem sum_rectanglePentagonWeight_eq_sum_pentagonRectangleWeight_iff_sdiff_initialOverlap
    (R : Type*) [CommSemiring R] [IsCancelAdd R] (x z : GridState n) :
    (∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) =
        ∑ E ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R E ↔
      (∑ D ∈ G.rectanglePentagonDecompositions C x z \ G.initialOverlapSources C x z,
          G.rectanglePentagonWeight C R D) =
        ∑ E ∈ G.pentagonRectangleDecompositions C x z \ G.initialOverlapPartners C x z,
          G.pentagonRectangleWeight C R E := by
  classical
  rw [← Finset.sum_sdiff
      (G.initialOverlapSources_subset_rectanglePentagonDecompositions C (x := x) (z := z))
      (f := G.rectanglePentagonWeight C R),
    ← Finset.sum_sdiff
      (G.initialOverlapPartners_subset_pentagonRectangleDecompositions C (x := x) (z := z))
      (f := G.pentagonRectangleWeight C R),
    G.sum_rectanglePentagonWeight_initialOverlapSources_eq_sum_pentagonRectangleWeight_partners
      C R x z]
  exact add_right_cancel_iff

end TauCeti.GridDiagram
