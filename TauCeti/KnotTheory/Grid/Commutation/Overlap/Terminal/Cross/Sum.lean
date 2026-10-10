/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Counted
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Weight

/-!
# Removing terminal-side cross-overlap contributions from the pentagon chain-map equation

A counted rectangle followed by a pentagon with a common terminal side recuts across the
chain-map equation when the pentagon's initial side lies strictly inside the rectangle's
column interval. In this column order the first recut rectangle inherits the common
terminal side, and promoting it gives a counted pentagon followed by a rectangle.

`GridDiagram.terminalCrossOverlapPartners` is the exact recut image of
`GridDiagram.terminalCrossOverlapSources`. The recut is injective and preserves weights,
so the total contributions of these families agree over any commutative semiring. Over a
semiring with cancellative addition, removing them preserves the full coefficient equation.
The membership characterization of the partner family uses an existing source and the
underlying recut relation; it does not assert exhaustiveness among all overlapping terms.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
[Section 3.1, Lemma 3.1](https://arxiv.org/abs/math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  {x z : GridState n}

/-- The counted common-terminal-side rectangle--pentagon decompositions whose recuts
cross to the pentagon--rectangle sum. The initial side of the pentagon lies strictly inside
the rectangle's column interval. -/
noncomputable def terminalCrossOverlapSources (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectanglePentagonDecompositions C x z).filter fun D =>
    D.rectangle.right = D.pentagon.right ∧
      D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right

/-- A terminal cross-overlap source is a counted term with the indicated terminal side
and column order. -/
@[simp]
theorem mem_terminalCrossOverlapSources
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.terminalCrossOverlapSources C x z ↔
      D ∈ G.rectanglePentagonDecompositions C x z ∧
        D.rectangle.right = D.pentagon.right ∧
          D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right := by
  classical
  simp [terminalCrossOverlapSources]

private theorem terminalCrossOverlapSource_data
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.terminalCrossOverlapSources C x z) :
    D.rectangle.right = D.pentagon.right ∧
      D.toRectangleDecomposition.HasOneCommonSide ∧
        D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty := by
  obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_terminalCrossOverlapSources C D).1 hD
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcounted
  exact ⟨hcommon,
    D.hasOneCommonSide_of_right_eq_right hcommon (Grid.ne_left_of_mem_cIoo hcol).symm,
    ((G.mem_unblockedRectangles _).1 hr).1, ((G.mem_pentagons _).1 hP).1⟩

private theorem terminalCrossOverlapSource_first_right
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.terminalCrossOverlapSources C x z) :
    (D.recutOfIsEmpty (G.terminalCrossOverlapSource_data C D hD).2.1
      (G.terminalCrossOverlapSource_data C D hD).2.2.1
      (G.terminalCrossOverlapSource_data C D hD).2.2.2).first.right =
        D.pentagon.right := by
  obtain ⟨_, hcommon, hcol⟩ := (G.mem_terminalCrossOverlapSources C D).1 hD
  obtain ⟨_, hone, hr, hP⟩ := G.terminalCrossOverlapSource_data C D hD
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hr hP
  rw [← D.recutOfIsEmpty_eq_recut hone hr hP] at hdata
  rcases hdata.recut_branch with h | h
  · have hcol' : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right := by
      simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
        hcommon] using h.1
    exact False.elim (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap D.rectangle.left D.pentagon.right)
      hcol (Grid.mem_cIoo_cyclic_right hcol'))
  · exact h.2.2.1.trans (D.toRectangleDecomposition_first_right.trans hcommon)

private theorem terminalCrossOverlapSource_underlying_isEmpty
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.terminalCrossOverlapSources C x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨_, _, hr, hP⟩ := G.terminalCrossOverlapSource_data C D hD
  constructor
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hr
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
      using hP

private noncomputable def terminalCrossOverlapPartner
    (D : {D // D ∈ G.terminalCrossOverlapSources C x z}) :
    GridPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutRightEqRightFirst
    (G.terminalCrossOverlapSource_data C D.val D.property).1
    (G.terminalCrossOverlapSource_data C D.val D.property).2.1
    (G.terminalCrossOverlapSource_data C D.val D.property).2.2.1
    (G.terminalCrossOverlapSource_data C D.val D.property).2.2.2
    (G.terminalCrossOverlapSource_first_right C D.val D.property)

private theorem terminalCrossOverlapPartner_isRecut
    (D : {D // D ∈ G.terminalCrossOverlapSources C x z}) :
    D.val.toRectangleDecomposition.IsRecut
      (G.terminalCrossOverlapPartner C D).toRectangleDecomposition := by
  unfold terminalCrossOverlapPartner
  exact D.val.isRecut_recutRightEqRightFirst _ _ _ _ _

private theorem terminalCrossOverlapPartner_injective :
    Function.Injective (G.terminalCrossOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.terminalCrossOverlapPartner_isRecut C D
  have hE := G.terminalCrossOverlapPartner_isRecut C E
  rw [← h] at hE
  have honeD := (G.terminalCrossOverlapSource_data C D.val D.property).2.1
  have honeE := (G.terminalCrossOverlapSource_data C E.val E.property).2.1
  obtain ⟨hfD, hsD⟩ := G.terminalCrossOverlapSource_underlying_isEmpty C D.val D.property
  obtain ⟨hfE, hsE⟩ := G.terminalCrossOverlapSource_underlying_isEmpty C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

private theorem terminalCrossOverlapPartner_mem
    (D : {D // D ∈ G.terminalCrossOverlapSources C x z}) :
    G.terminalCrossOverlapPartner C D ∈ G.pentagonRectangleDecompositions C x z := by
  obtain ⟨hcounted, _, _⟩ := (G.mem_terminalCrossOverlapSources C D.val).1 D.property
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D.val).1 hcounted
  unfold terminalCrossOverlapPartner
  exact G.recutRightEqRightFirst_mem_pentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_unblockedRectangles _).1 hr).2 ((G.mem_pentagons _).1 hP).2 _

/-- The pentagon--rectangle partners obtained by recutting the counted terminal cross-overlap
sources. This family is the exact recut image of `terminalCrossOverlapSources`. -/
noncomputable def terminalCrossOverlapPartners (x z : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.terminalCrossOverlapSources C x z).attach.map
    ⟨G.terminalCrossOverlapPartner C, G.terminalCrossOverlapPartner_injective C⟩

/-- A pentagon--rectangle term is a partner exactly when its underlying rectangles are the
recut of a counted terminal cross-overlap source. -/
@[simp]
theorem mem_terminalCrossOverlapPartners
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.terminalCrossOverlapPartners C x z ↔
      ∃ D ∈ G.terminalCrossOverlapSources C x z,
        D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [terminalCrossOverlapPartners, Finset.mem_map, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.terminalCrossOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    have hone := (G.terminalCrossOverlapSource_data C D hD).2.1
    obtain ⟨hf, hs⟩ := G.terminalCrossOverlapSource_underlying_isEmpty C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
    exact (D.toRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
      (G.terminalCrossOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Each terminal cross-overlap source belongs to the full rectangle--pentagon coefficient sum. -/
theorem terminalCrossOverlapSources_subset_rectanglePentagonDecompositions :
    G.terminalCrossOverlapSources C x z ⊆ G.rectanglePentagonDecompositions C x z := by
  intro D hD
  exact ((G.mem_terminalCrossOverlapSources C D).1 hD).1

/-- Each partner belongs to the full pentagon--rectangle coefficient sum. -/
theorem terminalCrossOverlapPartners_subset_pentagonRectangleDecompositions :
    G.terminalCrossOverlapPartners C x z ⊆ G.pentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [terminalCrossOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  exact G.terminalCrossOverlapPartner_mem C D

/-- Recutting identifies the total terminal cross-overlap source contribution with the total
contribution of its pentagon--rectangle partners over any commutative coefficient semiring. -/
theorem sum_rectanglePentagonWeight_terminalCrossOverlapSources_eq_sum_partners
    (R : Type*) [CommSemiring R] (x z : GridState n) :
    ∑ D ∈ G.terminalCrossOverlapSources C x z, G.rectanglePentagonWeight C R D =
      ∑ E ∈ G.terminalCrossOverlapPartners C x z, G.pentagonRectangleWeight C R E := by
  classical
  have hweight (D : {D // D ∈ G.terminalCrossOverlapSources C x z}) :
      G.pentagonRectangleWeight C R (G.terminalCrossOverlapPartner C D) =
        G.rectanglePentagonWeight C R D.val := by
    unfold terminalCrossOverlapPartner
    exact G.pentagonRectangleWeight_recutRightEqRightFirst C R D.val _ _ _ _ _
  rw [terminalCrossOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, hweight, Finset.sum_attach]

open scoped Classical in
/-- The two full pentagon chain-map coefficient sums agree exactly when their complements
after removing the terminal cross-overlap sources and their recut partners agree. -/
theorem sum_rectanglePentagonWeight_eq_sum_pentagonRectangleWeight_iff_sdiff_terminalCrossOverlap
    (R : Type*) [CommSemiring R] [IsCancelAdd R] (x z : GridState n) :
    (∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) =
        ∑ E ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R E ↔
      (∑ D ∈ G.rectanglePentagonDecompositions C x z \ G.terminalCrossOverlapSources C x z,
          G.rectanglePentagonWeight C R D) =
        ∑ E ∈ G.pentagonRectangleDecompositions C x z \ G.terminalCrossOverlapPartners C x z,
          G.pentagonRectangleWeight C R E := by
  classical
  rw [← Finset.sum_sdiff
      (G.terminalCrossOverlapSources_subset_rectanglePentagonDecompositions C (x := x) (z := z))
      (f := G.rectanglePentagonWeight C R),
    ← Finset.sum_sdiff
      (G.terminalCrossOverlapPartners_subset_pentagonRectangleDecompositions C (x := x) (z := z))
      (f := G.pentagonRectangleWeight C R),
    G.sum_rectanglePentagonWeight_terminalCrossOverlapSources_eq_sum_partners
      C R x z]
  exact add_right_cancel_iff

end TauCeti.GridDiagram
