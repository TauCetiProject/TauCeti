/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Pairing
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.PentagonTerminal.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Cancellation of terminal self-pairs in the pentagon--rectangle sum

A pentagon followed by a rectangle with the same terminal side has a self-recut when
the rectangle's initial side lies in the pentagon's column interval. The recut gives a
distinct counted pentagon--rectangle term with the same weight and a mixed common side.
The source and partner families are disjoint and the partner construction is injective.
Thus the whole family contributes zero in characteristic two and can be removed from
the pentagon chain-map coefficient equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- Counted pentagon--rectangle terms with a common terminal side whose recuts stay in the
same coefficient sum. -/
noncomputable def pentagonTerminalSelfPairSources (x z : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.pentagonRectangleDecompositions C x z).filter fun D =>
    D.rectangle.right = D.pentagon.right ∧
      D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right

/-- Membership records counting and the common-terminal-side column order. -/
@[simp]
theorem mem_pentagonTerminalSelfPairSources
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    D ∈ G.pentagonTerminalSelfPairSources C x z ↔
      D ∈ G.pentagonRectangleDecompositions C x z ∧
        D.rectangle.right = D.pentagon.right ∧
          D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right := by
  classical
  simp [pentagonTerminalSelfPairSources]

private theorem pentagonTerminalSource_data
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.pentagonTerminalSelfPairSources C x z) :
    D.rectangle.right = D.pentagon.right ∧
      D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right ∧
        D.pentagon.IsEmpty ∧ D.rectangle.IsEmpty := by
  obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_pentagonTerminalSelfPairSources C D).1 hD
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C D).1 hcounted
  exact ⟨hcommon, hcol, ((G.mem_pentagons _).1 hP).1,
    (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1⟩

private noncomputable def pentagonTerminalPartner
    (D : {D // D ∈ G.pentagonTerminalSelfPairSources C x z}) :
    GridPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutTerminal (G.pentagonTerminalSource_data C D.val D.property).1
    (G.pentagonTerminalSource_data C D.val D.property).2.1
    (G.pentagonTerminalSource_data C D.val D.property).2.2.1
    (G.pentagonTerminalSource_data C D.val D.property).2.2.2

private theorem pentagonTerminalPartner_isRecut
    (D : {D // D ∈ G.pentagonTerminalSelfPairSources C x z}) :
    D.val.toRectangleDecomposition.IsRecut
      (G.pentagonTerminalPartner C D).toRectangleDecomposition := by
  unfold pentagonTerminalPartner
  exact D.val.isRecut_recutTerminal _ _ _ _

private theorem pentagonTerminalSource_underlying
    (D : {D // D ∈ G.pentagonTerminalSelfPairSources C x z}) :
    D.val.toRectangleDecomposition.HasOneCommonSide ∧
      D.val.toRectangleDecomposition.first.IsEmpty ∧
        D.val.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨hcommon, hcol, hp, hr⟩ := G.pentagonTerminalSource_data C D.val D.property
  refine ⟨?_, ?_, ?_⟩
  · exact D.val.hasOneCommonSide_of_terminal_overlap hcommon hcol
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle] using hp
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle] using hr

private theorem pentagonTerminalPartner_injective :
    Function.Injective (G.pentagonTerminalPartner C (x := x) (z := z)) := by
  intro D F h
  have hD := G.pentagonTerminalPartner_isRecut C D
  have hF := G.pentagonTerminalPartner_isRecut C F
  rw [← h] at hF
  obtain ⟨honeD, hpD, hrD⟩ := G.pentagonTerminalSource_underlying C D
  obtain ⟨honeF, hpF, hrF⟩ := G.pentagonTerminalSource_underlying C F
  have hbackD := hD.symm honeD hpD hrD
  have hbackF := hF.symm honeF hpF hrF
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackF

private theorem pentagonTerminalPartner_mem
    (D : {D // D ∈ G.pentagonTerminalSelfPairSources C x z}) :
    G.pentagonTerminalPartner C D ∈ G.pentagonRectangleDecompositions C x z := by
  unfold pentagonTerminalPartner
  exact G.recutTerminal_mem_pentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_pentagonTerminalSelfPairSources C D.val).1 D.property).1

private theorem pentagonTerminalPartner_notMem
    (D : {D // D ∈ G.pentagonTerminalSelfPairSources C x z}) :
    G.pentagonTerminalPartner C D ∉ G.pentagonTerminalSelfPairSources C x z := by
  intro h
  have hcommon := ((G.mem_pentagonTerminalSelfPairSources C _).1 h).2.1
  obtain ⟨hcommonD, hcol, hp, hr⟩ := G.pentagonTerminalSource_data C D.val D.property
  have hright := (D.val.recutTerminal_geometry hcommonD hcol hp hr).2.2.2.2.2
  have hne := Grid.ne_right_of_mem_cIoo hcol
  exact hne (hright.symm.trans (hcommon.trans
    ((G.pentagonTerminalPartner C D).pentagon.right_eq.trans
      D.val.pentagon.right_eq.symm)))

/-- The terminal self-pairs consist of the common-terminal-side sources and their distinct,
counted recuts in the pentagon--rectangle coefficient sum. -/
noncomputable def pentagonTerminalSelfPairs (x z : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.pentagonTerminalSelfPairSources C x z).withPartners
    ⟨G.pentagonTerminalPartner C, G.pentagonTerminalPartner_injective C⟩

/-- Membership in the self-pair family is membership in the source family or being the
underlying recut of a source. -/
@[simp]
theorem mem_pentagonTerminalSelfPairs
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.pentagonTerminalSelfPairs C x z ↔
      E ∈ G.pentagonTerminalSelfPairSources C x z ∨
        ∃ D ∈ G.pentagonTerminalSelfPairSources C x z,
          D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [pentagonTerminalSelfPairs, Finset.mem_withPartners, Function.Embedding.coeFn_mk]
  apply or_congr_right
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.pentagonTerminalPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨hone, hp, hr⟩ := G.pentagonTerminalSource_underlying C ⟨D, hD⟩
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
    exact (D.toRectangleDecomposition.existsUnique_isRecut hone hp hr).unique
      (G.pentagonTerminalPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Every terminal self-pair term is counted in the pentagon--rectangle coefficient sum. -/
theorem pentagonTerminalSelfPairs_subset_pentagonRectangleDecompositions :
    G.pentagonTerminalSelfPairs C x z ⊆ G.pentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [pentagonTerminalSelfPairs, Finset.mem_withPartners] at hE
  rcases hE with hE | hE
  · exact ((G.mem_pentagonTerminalSelfPairSources C E).1 hE).1
  · obtain ⟨D, rfl⟩ := hE
    exact G.pentagonTerminalPartner_mem C D

/-- The terminal self-pairs cancel in characteristic two. The two families are disjoint and
their contributions agree term by term under an injective recut. -/
theorem sum_pentagonRectangleWeight_pentagonTerminalSelfPairs_eq_zero
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    ∑ D ∈ G.pentagonTerminalSelfPairs C x z, G.pentagonRectangleWeight C R D = 0 := by
  classical
  have hw (D : {D // D ∈ G.pentagonTerminalSelfPairSources C x z}) :
      G.pentagonRectangleWeight C R (G.pentagonTerminalPartner C D) =
        G.pentagonRectangleWeight C R D.val := by
    unfold pentagonTerminalPartner
    exact G.pentagonRectangleWeight_recutTerminal C R D.val _ _ _ _
  apply Finset.sum_withPartners_eq_zero (G.pentagonTerminalSelfPairSources C x z)
    ⟨G.pentagonTerminalPartner C, G.pentagonTerminalPartner_injective C⟩
    (G.pentagonRectangleWeight C R) (G.pentagonTerminalPartner_notMem C)
  intro D
  simpa only [Function.Embedding.coeFn_mk, hw] using
    (CharTwo.add_self_eq_zero (G.pentagonRectangleWeight C R D.val))

open scoped Classical in
/-- Remove the terminal self-pairs from the pentagon--rectangle coefficient sum. -/
theorem sum_pentagonRectangleWeight_eq_sum_sdiff_pentagonTerminalSelfPairs
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    (∑ D ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R D) =
      ∑ D ∈ G.pentagonRectangleDecompositions C x z \ G.pentagonTerminalSelfPairs C x z,
        G.pentagonRectangleWeight C R D := by
  classical
  have h := Finset.sum_sdiff (G.pentagonTerminalSelfPairs_subset_pentagonRectangleDecompositions C
    (x := x) (z := z)) (f := G.pentagonRectangleWeight C R)
  rw [G.sum_pentagonRectangleWeight_pentagonTerminalSelfPairs_eq_zero C R x z, add_zero] at h
  exact h.symm

open scoped Classical in
/-- The pentagon map commutes with the differentials on a generator exactly when the
coefficient sums agree after discarding the pentagon--rectangle terminal self-pairs. -/
theorem pentagonMap_unblockedDifferential_single_eq_iff_sdiff_pentagonTerminalSelfPairs
    (R : Type*) [CommSemiring R] [CharP R 2] (x : GridState n) :
    G.pentagonMap R C (G.unblockedDifferential R (Finsupp.single x 1)) =
        (G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R
          (G.pentagonMap R C (Finsupp.single x 1)) ↔
      ∀ z : GridState n,
        (∑ D ∈ G.rectanglePentagonDecompositions C x z,
            G.rectanglePentagonWeight C R D) =
          ∑ D ∈ G.pentagonRectangleDecompositions C x z \ G.pentagonTerminalSelfPairs C x z,
            G.pentagonRectangleWeight C R D := by
  rw [G.pentagonMap_unblockedDifferential_single_eq_iff C R]
  simp_rw [G.sum_pentagonRectangleWeight_eq_sum_sdiff_pentagonTerminalSelfPairs C R]

end TauCeti.GridDiagram
