/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Pairing
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Pairing
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Weight
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Cancellation of terminal-overlap self-pairs

In the pentagon chain-map equation, a rectangle followed by a pentagon with a common
terminal side can recut to another rectangle followed by a pentagon. This happens exactly
when the rectangle's initial side lies inside the pentagon's column interval. The partner
has a mixed common side: the rectangle's terminal side is the pentagon's initial side.
Consequently the sources and partners are disjoint families, not two terms on opposite
sides of the chain-map equation.

This file collects these sources and their recuts into `GridDiagram.terminalSelfPairs`.
The recut is injective, both terms are counted, and their weights agree. Their total
contribution therefore vanishes in characteristic two. The final theorem removes this
whole family from the rectangle--pentagon coefficient sum. Other overlap orientations
and the pairing with the pentagon--rectangle sum are not addressed here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  {x z : GridState n}

/-- The counted common-terminal-side rectangle--pentagon domains whose recuts stay in the
rectangle--pentagon sum. The initial side of the rectangle is strictly inside the
pentagon's column interval. -/
noncomputable def terminalSelfPairSources (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectanglePentagonDecompositions C x z).filter fun D =>
    D.rectangle.right = D.pentagon.right ∧
      D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right

/-- A source of a terminal self-pair is a counted term with the indicated terminal side
and column order. -/
@[simp]
theorem mem_terminalSelfPairSources
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.terminalSelfPairSources C x z ↔
      D ∈ G.rectanglePentagonDecompositions C x z ∧
        D.rectangle.right = D.pentagon.right ∧
          D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right := by
  classical
  simp [terminalSelfPairSources]

private theorem terminalSelfPairSource_data
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.terminalSelfPairSources C x z) :
    D.rectangle.right = D.pentagon.right ∧
      D.toRectangleDecomposition.HasOneCommonSide ∧
        D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty := by
  obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_terminalSelfPairSources C D).1 hD
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcounted
  exact ⟨hcommon, D.hasOneCommonSide_of_right_eq_right hcommon (Grid.ne_left_of_mem_cIoo hcol),
    ((G.mem_unblockedRectangles _).1 hr).1, ((G.mem_pentagons _).1 hP).1⟩

private theorem terminalSelfPairSource_second_right
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.terminalSelfPairSources C x z) :
    (D.recutOfIsEmpty (G.terminalSelfPairSource_data C D hD).2.1
      (G.terminalSelfPairSource_data C D hD).2.2.1
      (G.terminalSelfPairSource_data C D hD).2.2.2).second.right = D.pentagon.right := by
  obtain ⟨_, hcommon, hcol⟩ := (G.mem_terminalSelfPairSources C D).1 hD
  obtain ⟨_, hone, hr, hP⟩ := G.terminalSelfPairSource_data C D hD
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hr hP
  rw [← D.recutOfIsEmpty_eq_recut hone hr hP] at hdata
  rcases hdata.recut_branch with h | h
  · exact h.2.2.2.trans (D.toRectangleDecomposition_first_right.trans hcommon)
  · have hcol' : D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right := by
      simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
        hcommon] using h.1
    exact False.elim (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap D.pentagon.left D.pentagon.right)
      hcol (Grid.mem_cIoo_cyclic_right hcol'))

private noncomputable def terminalSelfPairPartner
    (D : {D // D ∈ G.terminalSelfPairSources C x z}) :
    GridRectanglePentagonDecomposition C.column C.turnRow x z :=
  D.val.recutRightEqRightSecond
    (G.terminalSelfPairSource_data C D.val D.property).1
    (G.terminalSelfPairSource_data C D.val D.property).2.1
    (G.terminalSelfPairSource_data C D.val D.property).2.2.1
    (G.terminalSelfPairSource_data C D.val D.property).2.2.2
    (G.terminalSelfPairSource_second_right C D.val D.property)

private theorem terminalSelfPairPartner_isRecut
    (D : {D // D ∈ G.terminalSelfPairSources C x z}) :
    D.val.toRectangleDecomposition.IsRecut
      (G.terminalSelfPairPartner C D).toRectangleDecomposition := by
  unfold terminalSelfPairPartner
  exact D.val.isRecut_recutRightEqRightSecond _ _ _ _ _

private theorem terminalSelfPairPartner_injective :
    Function.Injective (G.terminalSelfPairPartner C (x := x) (z := z)) := by
  intro D E h
  apply Subtype.ext
  unfold terminalSelfPairPartner at h
  exact (GridRectanglePentagonDecomposition.recutRightEqRightSecond_inj
    _ _ _ _ _ _ _ _ _ _ _ _).1 h

private theorem terminalSelfPairPartner_mem
    (D : {D // D ∈ G.terminalSelfPairSources C x z}) :
    G.terminalSelfPairPartner C D ∈ G.rectanglePentagonDecompositions C x z := by
  obtain ⟨hcounted, _, _⟩ := (G.mem_terminalSelfPairSources C D.val).1 D.property
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D.val).1 hcounted
  unfold terminalSelfPairPartner
  exact G.recutRightEqRightSecond_mem_rectanglePentagonDecompositions C D.val _ _ _ _
    ((G.mem_unblockedRectangles _).1 hr).2 ((G.mem_pentagons _).1 hP).2 _

private theorem terminalSelfPairPartner_notMem
    (D : {D // D ∈ G.terminalSelfPairSources C x z}) :
    G.terminalSelfPairPartner C D ∉ G.terminalSelfPairSources C x z := by
  intro h
  have hcommon := ((G.mem_terminalSelfPairSources C _).1 h).2.1
  obtain ⟨_, _, hcol⟩ := (G.mem_terminalSelfPairSources C D.val).1 D.property
  obtain ⟨_, hright, _, _, _, _, _⟩ :=
    D.val.recutRightEqRightSecond_rectangle_geometry
      (G.terminalSelfPairSource_data C D.val D.property).1
      (G.terminalSelfPairSource_data C D.val D.property).2.1
      (G.terminalSelfPairSource_data C D.val D.property).2.2.1
      (G.terminalSelfPairSource_data C D.val D.property).2.2.2
      (G.terminalSelfPairSource_second_right C D.val D.property)
  have hpartnerRight : (G.terminalSelfPairPartner C D).rectangle.right = D.val.rectangle.left :=
    hright
  exact Grid.ne_right_of_mem_cIoo hcol
    (hpartnerRight.symm.trans (hcommon.trans
      ((G.terminalSelfPairPartner C D).pentagon.right_eq.trans D.val.pentagon.right_eq.symm)))

/-- All terminal self-pairs: the common-terminal-side sources and their distinct counted
rectangle--pentagon recuts. -/
noncomputable def terminalSelfPairs (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.terminalSelfPairSources C x z).withPartners
    ⟨G.terminalSelfPairPartner C, G.terminalSelfPairPartner_injective C⟩

/-- The family of terminal self-pairs consists of sources and recuts of sources, with the
recut relation on the underlying rectangles specifying the partner uniquely. -/
@[simp]
theorem mem_terminalSelfPairs
    (E : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    E ∈ G.terminalSelfPairs C x z ↔
      E ∈ G.terminalSelfPairSources C x z ∨
        ∃ D ∈ G.terminalSelfPairSources C x z,
          D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [terminalSelfPairs, Finset.mem_withPartners, Function.Embedding.coeFn_mk]
  apply or_congr_right
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.terminalSelfPairPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨_, hone, hr, hP⟩ := G.terminalSelfPairSource_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
    exact (D.toRectangleDecomposition.existsUnique_isRecut hone
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hr)
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
        using hP)).unique (G.terminalSelfPairPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Every term of a terminal self-pair is counted in the rectangle--pentagon coefficient. -/
theorem terminalSelfPairs_subset_rectanglePentagonDecompositions :
    G.terminalSelfPairs C x z ⊆ G.rectanglePentagonDecompositions C x z := by
  classical
  intro E hE
  rw [terminalSelfPairs, Finset.mem_withPartners] at hE
  rcases hE with hE | hE
  · exact ((G.mem_terminalSelfPairSources C E).1 hE).1
  · obtain ⟨D, rfl⟩ := hE
    exact G.terminalSelfPairPartner_mem C D

/-- The contributions of the terminal self-pairs cancel in characteristic two. No domain
is counted twice: the source family and its injectively indexed partner family are disjoint. -/
theorem sum_rectanglePentagonWeight_terminalSelfPairs_eq_zero
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    ∑ D ∈ G.terminalSelfPairs C x z, G.rectanglePentagonWeight C R D = 0 := by
  classical
  have hweight (D : {D // D ∈ G.terminalSelfPairSources C x z}) :
      G.rectanglePentagonWeight C R (G.terminalSelfPairPartner C D) =
        G.rectanglePentagonWeight C R D.val := by
    unfold terminalSelfPairPartner
    exact G.rectanglePentagonWeight_recutRightEqRightSecond C R D.val _ _ _ _ _
  apply Finset.sum_withPartners_eq_zero (G.terminalSelfPairSources C x z)
    ⟨G.terminalSelfPairPartner C, G.terminalSelfPairPartner_injective C⟩
    (G.rectanglePentagonWeight C R) (G.terminalSelfPairPartner_notMem C)
  intro D
  simpa only [Function.Embedding.coeFn_mk, hweight] using
    (CharTwo.add_self_eq_zero (G.rectanglePentagonWeight C R D.val))

open scoped Classical in
/-- Remove the terminal self-pairs from the rectangle--pentagon side of the pentagon
chain-map equation over a coefficient semiring of characteristic two. -/
theorem sum_rectanglePentagonWeight_eq_sum_sdiff_terminalSelfPairs
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    (∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) =
      ∑ D ∈ G.rectanglePentagonDecompositions C x z \ G.terminalSelfPairs C x z,
        G.rectanglePentagonWeight C R D := by
  classical
  have h := Finset.sum_sdiff (G.terminalSelfPairs_subset_rectanglePentagonDecompositions C
    (x := x) (z := z)) (f := G.rectanglePentagonWeight C R)
  rw [G.sum_rectanglePentagonWeight_terminalSelfPairs_eq_zero C R x z, add_zero] at h
  exact h.symm

end TauCeti.GridDiagram
