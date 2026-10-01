/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Marking
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.RectangleMarking

/-!
# Counted partners in the terminal-side self-pairing

In the pentagon chain-map equation, a rectangle followed by a pentagon sharing their terminal
side can recut to another rectangle followed by a pentagon. This happens when the second
rectangle of the recut inherits the replaced grid line. The two terms belong to the same
coefficient sum, rather than to opposite sides of the equation.

This file proves that this partner is counted by the original diagram's differential and
pentagon map. The remaining rectangle avoids both columns involved in the commutation, so
its previously established avoidance in the commuted diagram also gives avoidance in the
original diagram. The partner is unique among counted recuts, has a different intermediate
state, and determines the original term. Thus this branch supplies distinct, unambiguous terms
for the same-sum cancellation;
the weight identity and assembly of the full overlap pairing are separate arguments.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  {x z : GridState n}

/-- The terminal-side recut whose second rectangle becomes a pentagon is counted in the
same rectangle--pentagon family as the original term. -/
theorem recutRightEqRightSecond_mem_rectanglePentagonDecompositions
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet)
    (hPX : Disjoint D.pentagon.coveredSquares G.XSet)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
      D.pentagon.right) :
    D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond ∈
      G.rectanglePentagonDecompositions C x z := by
  rw [G.mem_rectanglePentagonDecompositions C]
  refine ⟨(G.mem_unblockedRectangles _).2 ⟨?_, ?_⟩,
    (G.mem_pentagons _).2 ⟨?_, ?_⟩⟩
  · exact D.isEmpty_rectangle_recutRightEqRightSecond
      hcommon hone hrectangle hpentagon hsecond
  · obtain ⟨_, _, _, _, _, ha, hb⟩ :=
      D.recutRightEqRightSecond_rectangle_geometry hcommon hone hrectangle hpentagon hsecond
    exact (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns _
      (iff_of_false ha hb)).1
        (D.disjoint_coveredSquares_XSet_rectangle_recutRightEqRightSecond
          hcommon hone hrectangle hpentagon hsecond G hPX)
  · exact D.isEmpty_pentagon_recutRightEqRightSecond
      hcommon hone hrectangle hpentagon hsecond
  · exact D.disjoint_coveredSquares_XSet_pentagon_recutRightEqRightSecond
      hcommon hone hrectangle hpentagon hsecond G hPX hrectX

/-- A counted common-terminal-side term whose second recut rectangle inherits the replaced
grid line has exactly one counted rectangle--pentagon recut. Its intermediate state differs
from that of the original term, as recorded by `GridRectangleDecomposition.IsRecut.middle_ne`.
-/
theorem existsUnique_counted_recut_of_right_eq_right_second
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hsecond : ∀ (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty),
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.right) :
    ∃! E : GridRectanglePentagonDecomposition C.column C.turnRow x z,
      E ∈ G.rectanglePentagonDecompositions C x z ∧
        D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  obtain ⟨hrectangle, hpentagon⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hD
  obtain ⟨hrectangle, hrectX⟩ := (G.mem_unblockedRectangles _).1 hrectangle
  obtain ⟨hpentagon, hPX⟩ := (G.mem_pentagons _).1 hpentagon
  let E := D.recutRightEqRightSecond hcommon hone hrectangle hpentagon
    (hsecond hrectangle hpentagon)
  refine ⟨E, ⟨G.recutRightEqRightSecond_mem_rectanglePentagonDecompositions C D
    hcommon hone hrectangle hpentagon hrectX hPX _,
    D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon _⟩, ?_⟩
  intro F hF
  apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
  have hfirst : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  have hlast : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle,
      D.toRectangleDecomposition_second_toGridRectangle] using hpentagon
  exact (D.toRectangleDecomposition.existsUnique_isRecut hone hfirst hlast).unique
    hF.2 (D.isRecut_recutRightEqRightSecond hcommon hone hrectangle hpentagon _)

end TauCeti.GridDiagram

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The terminal-side second-rectangle promotion does not identify distinct terms: equality
of the promoted recuts is equivalent to equality of the original decompositions. -/
@[simp]
theorem recutRightEqRightSecond_eq_iff
    (D E : GridRectanglePentagonDecomposition a s x z)
    (hcommonD : D.rectangle.right = D.pentagon.right)
    (hcommonE : E.rectangle.right = E.pentagon.right)
    (honeD : D.toRectangleDecomposition.HasOneCommonSide)
    (honeE : E.toRectangleDecomposition.HasOneCommonSide)
    (hrectangleD : D.rectangle.IsEmpty) (hpentagonD : D.pentagon.IsEmpty)
    (hrectangleE : E.rectangle.IsEmpty) (hpentagonE : E.pentagon.IsEmpty)
    (hsecondD : (D.recutOfIsEmpty honeD hrectangleD hpentagonD).second.right =
      D.pentagon.right)
    (hsecondE : (E.recutOfIsEmpty honeE hrectangleE hpentagonE).second.right =
      E.pentagon.right) :
    D.recutRightEqRightSecond hcommonD honeD hrectangleD hpentagonD hsecondD =
        E.recutRightEqRightSecond hcommonE honeE hrectangleE hpentagonE hsecondE ↔ D = E := by
  constructor
  · intro h
    have hD := D.isRecut_recutRightEqRightSecond
      hcommonD honeD hrectangleD hpentagonD hsecondD
    have hE := E.isRecut_recutRightEqRightSecond
      hcommonE honeE hrectangleE hpentagonE hsecondE
    rw [← h] at hE
    have hfirstD : D.toRectangleDecomposition.first.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_first_toGridRectangle] using hrectangleD
    have hlastD : D.toRectangleDecomposition.second.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle]
        using hpentagonD
    have hfirstE : E.toRectangleDecomposition.first.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_first_toGridRectangle] using hrectangleE
    have hlastE : E.toRectangleDecomposition.second.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle]
        using hpentagonE
    have hbackD := hD.symm honeD hfirstD hlastD
    have hbackE := hE.symm honeE hfirstE hlastE
    have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
      (D.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
    apply toRectangleDecomposition_injective
    exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
      hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE
  · rintro rfl
    rfl

end TauCeti.GridRectanglePentagonDecomposition
