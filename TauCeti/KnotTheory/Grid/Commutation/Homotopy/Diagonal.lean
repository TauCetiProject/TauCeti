/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Annulus

/-!
# The diagonal coefficient of the commutation homotopy anticommutator

A returning empty hexagon--rectangle domain is a thin annulus in one of the two columns
adjacent to the replaced grid line. Each turn side admits at most one such annulus. Its
existence is determined by whether the two turn rows occur in order between the state rows
on the sides of that column. The same description applies to a rectangle followed by a
hexagon, with those state rows exchanged.

This file counts the actual finite decomposition families and evaluates their weighted
sums as four explicit cyclic-interval tests. The formulas hold over any commutative semiring:
every counted annulus has weight one. They compute the diagonal coefficient of
`∂H + H∂`; identifying it with the diagonal coefficient of `1 + ΨΦ` additionally requires
the classification of returning pentagon pairs.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti
namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "c" => finRotate n (finRotate n C.column)

private theorem hexagonRectangle_side_inj (x : GridState n) :
    Set.InjOn (fun D : GridHexagonRectangleDecomposition a C.turnRow C.oppositeTurnRow x x =>
      D.hexagon.isLeft) (G.hexagonRectangleDecompositions C x x) := by
  rintro ⟨m, P, r⟩ hD ⟨m', Q, t⟩ hE hside
  have hD := (G.mem_hexagonRectangleDecompositions_diagonal_iff C _).mp hD
  have hE := (G.mem_hexagonRectangleDecompositions_diagonal_iff C _).mp hE
  simp only [GridHexagonRectangleDecomposition.hexagon,
    GridHexagonRectangleDecomposition.rectangle] at *
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hD hE
      cases P.sigma_target_eq_of_isEmpty_and_isEmpty r Q t hD hE
      rfl
    | inr Q => simp at hside
  | inr P =>
    cases Q with
    | inl Q => simp at hside
    | inr Q =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hD hE
      cases P.sigma_target_eq_of_isEmpty_and_isEmpty r Q t hD hE
      rfl

private theorem exists_hexagonRectangle_side_iff (x : GridState n) (i : Bool) :
    (∃ D ∈ G.hexagonRectangleDecompositions C x x, D.hexagon.isLeft = i) ↔
      if i then
        C.oppositeTurnRow ∈ Grid.cIco (x a) (x b) ∧
          C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x b)
      else
        C.turnRow ∈ Grid.cIco (x b) (x c) ∧
          C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x c) := by
  constructor
  -- The thin-annulus classification fixes both columns; the hexagon then supplies the row tests.
  · rintro ⟨⟨m, P, r⟩, hD, hi⟩
    have hempty := (G.mem_hexagonRectangleDecompositions_diagonal_iff C _).mp hD
    simp only [GridHexagonRectangleDecomposition.hexagon,
      GridHexagonRectangleDecomposition.rectangle] at hempty hi
    cases P with
    | inl P =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hempty
      have h := (GridHexagonBetween.exists_target_isEmpty_and_isEmpty_iff
        C.column_ne_next).mp ⟨m, P, r, hempty⟩
      cases i <;> simp_all only [Sum.isLeft_inl, Bool.true_eq_false, ite_true, and_self]
    | inr P =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hempty
      have h := (GridInitialHexagonBetween.exists_target_isEmpty_and_isEmpty_iff
        C.column_ne_next).mp ⟨m, P, r, hempty⟩
      cases i <;> simp_all only [Sum.isLeft_inr, Bool.false_eq_true, ite_false, and_self]
  -- Conversely the row tests construct the hexagon on the corresponding column annulus.
  · cases i with
    | true =>
      rintro ⟨hs, ht⟩
      obtain ⟨m, P, r, h⟩ := (GridHexagonBetween.exists_target_isEmpty_and_isEmpty_iff
        C.column_ne_next).mpr ⟨hs, ht⟩
      refine ⟨⟨m, Sum.inl P, r⟩, ?_, rfl⟩
      apply (G.mem_hexagonRectangleDecompositions_diagonal_iff C _).mpr
      simpa only [GridHexagonRectangleDecomposition.hexagon,
        GridHexagonRectangleDecomposition.rectangle,
        GridCommutationHexagonBetween.toGridRectangleBetween_inl] using h
    | false =>
      rintro ⟨hs, ht⟩
      obtain ⟨m, P, r, h⟩ := (GridInitialHexagonBetween.exists_target_isEmpty_and_isEmpty_iff
        C.column_ne_next).mpr ⟨hs, ht⟩
      refine ⟨⟨m, Sum.inr P, r⟩, ?_, rfl⟩
      apply (G.mem_hexagonRectangleDecompositions_diagonal_iff C _).mpr
      simpa only [GridHexagonRectangleDecomposition.hexagon,
        GridHexagonRectangleDecomposition.rectangle,
        GridCommutationHexagonBetween.toGridRectangleBetween_inr] using h

/-- The number of returning hexagon--rectangle annuli is the sum of the two ordered-turn
indicators, one for each column adjacent to the replaced line. -/
theorem card_hexagonRectangleDecompositions_diagonal (x : GridState n) :
    (G.hexagonRectangleDecompositions C x x).card =
      (if C.oppositeTurnRow ∈ Grid.cIco (x a) (x b) ∧
        C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x b) then 1 else 0) +
      (if C.turnRow ∈ Grid.cIco (x b) (x c) ∧
        C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x c) then 1 else 0) := by
  classical
  have himage : (G.hexagonRectangleDecompositions C x x).image
      (fun D => D.hexagon.isLeft) = Finset.univ.filter (fun i : Bool => if i then
        C.oppositeTurnRow ∈ Grid.cIco (x a) (x b) ∧
          C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x b)
        else C.turnRow ∈ Grid.cIco (x b) (x c) ∧
          C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x c)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact G.exists_hexagonRectangle_side_iff C x i
  rw [← Finset.card_image_of_injOn (G.hexagonRectangle_side_inj C x), himage]
  rw [Fintype.univ_bool]
  simp only [Finset.filter_insert, Finset.filter_singleton, Bool.coe_false,
    ite_true, ite_false]
  split_ifs <;> simp

private theorem rectangleHexagon_side_inj (x : GridState n) :
    Set.InjOn (fun D : GridRectangleHexagonDecomposition a C.turnRow C.oppositeTurnRow x x =>
      D.hexagon.isLeft) (G.rectangleHexagonDecompositions C x x) := by
  rintro ⟨m, r, P⟩ hD ⟨m', t, Q⟩ hE hside
  have hD := ((G.mem_rectangleHexagonDecompositions_diagonal_iff C _).mp hD).symm
  have hE := ((G.mem_rectangleHexagonDecompositions_diagonal_iff C _).mp hE).symm
  simp only [GridRectangleHexagonDecomposition.hexagon,
    GridRectangleHexagonDecomposition.rectangle] at *
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hD hE
      cases P.sigma_source_eq_of_isEmpty_and_isEmpty r Q t hD hE
      rfl
    | inr Q => simp at hside
  | inr P =>
    cases Q with
    | inl Q => simp at hside
    | inr Q =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hD hE
      cases P.sigma_source_eq_of_isEmpty_and_isEmpty r Q t hD hE
      rfl

private theorem exists_rectangleHexagon_side_iff (x : GridState n) (i : Bool) :
    (∃ D ∈ G.rectangleHexagonDecompositions C x x, D.hexagon.isLeft = i) ↔
      if i then
        C.oppositeTurnRow ∈ Grid.cIco (x b) (x a) ∧
          C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x a)
      else
        C.turnRow ∈ Grid.cIco (x c) (x b) ∧
          C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x b) := by
  constructor
  -- The returning rectangle exchanges the two state rows on the forced annulus columns.
  · rintro ⟨⟨m, r, P⟩, hD, hi⟩
    have hempty := ((G.mem_rectangleHexagonDecompositions_diagonal_iff C _).mp hD).symm
    simp only [GridRectangleHexagonDecomposition.hexagon,
      GridRectangleHexagonDecomposition.rectangle] at hempty hi
    cases P with
    | inl P =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hempty
      have h := (GridHexagonBetween.exists_source_isEmpty_and_isEmpty_iff
        C.column_ne_next).mp ⟨m, r, P, hempty⟩
      cases i <;> simp_all only [Sum.isLeft_inl, Bool.true_eq_false, ite_true, and_self]
    | inr P =>
      simp only [GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hempty
      have h := (GridInitialHexagonBetween.exists_source_isEmpty_and_isEmpty_iff
        C.column_ne_next).mp ⟨m, r, P, hempty⟩
      cases i <;> simp_all only [Sum.isLeft_inr, Bool.false_eq_true, ite_false, and_self]
  -- Build the outgoing rectangle by a column swap, then the returning hexagon on those sides.
  · cases i with
    | true =>
      rintro ⟨hs, ht⟩
      obtain ⟨m, r, P, h⟩ := (GridHexagonBetween.exists_source_isEmpty_and_isEmpty_iff
        C.column_ne_next).mpr ⟨hs, ht⟩
      refine ⟨⟨m, r, Sum.inl P⟩, ?_, rfl⟩
      apply (G.mem_rectangleHexagonDecompositions_diagonal_iff C _).mpr
      simpa only [GridRectangleHexagonDecomposition.hexagon,
        GridRectangleHexagonDecomposition.rectangle,
        GridCommutationHexagonBetween.toGridRectangleBetween_inl] using h.symm
    | false =>
      rintro ⟨hs, ht⟩
      obtain ⟨m, r, P, h⟩ := (GridInitialHexagonBetween.exists_source_isEmpty_and_isEmpty_iff
        C.column_ne_next).mpr ⟨hs, ht⟩
      refine ⟨⟨m, r, Sum.inr P⟩, ?_, rfl⟩
      apply (G.mem_rectangleHexagonDecompositions_diagonal_iff C _).mpr
      simpa only [GridRectangleHexagonDecomposition.hexagon,
        GridRectangleHexagonDecomposition.rectangle,
        GridCommutationHexagonBetween.toGridRectangleBetween_inr] using h.symm

/-- The number of returning rectangle--hexagon annuli is the sum of the two ordered-turn
indicators, one for each column adjacent to the replaced line. -/
theorem card_rectangleHexagonDecompositions_diagonal (x : GridState n) :
    (G.rectangleHexagonDecompositions C x x).card =
      (if C.oppositeTurnRow ∈ Grid.cIco (x b) (x a) ∧
        C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x a) then 1 else 0) +
      (if C.turnRow ∈ Grid.cIco (x c) (x b) ∧
        C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x b) then 1 else 0) := by
  classical
  have himage : (G.rectangleHexagonDecompositions C x x).image
      (fun D => D.hexagon.isLeft) = Finset.univ.filter (fun i : Bool => if i then
        C.oppositeTurnRow ∈ Grid.cIco (x b) (x a) ∧
          C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x a)
        else C.turnRow ∈ Grid.cIco (x c) (x b) ∧
          C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x b)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact G.exists_rectangleHexagon_side_iff C x i
  rw [← Finset.card_image_of_injOn (G.rectangleHexagon_side_inj C x), himage]
  rw [Fintype.univ_bool]
  simp only [Finset.filter_insert, Finset.filter_singleton, Bool.coe_false,
    ite_true, ite_false]
  split_ifs <;> simp

/-- The diagonal coefficient of `∂H + H∂` is the sum of four ordered-turn indicators.
The first two count hexagon--rectangle annuli and the last two count rectangle--hexagon
annuli. Each contribution is one over any commutative semiring. -/
theorem unblockedDifferential_commutationHomotopy_add_single_apply_self
    (R : Type*) [CommSemiring R] (x : GridState n) :
    (G.unblockedDifferential R (G.commutationHomotopy R C (Finsupp.single x 1)) +
        G.commutationHomotopy R C (G.unblockedDifferential R (Finsupp.single x 1))) x =
      ((if C.oppositeTurnRow ∈ Grid.cIco (x a) (x b) ∧
        C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x b) then 1 else 0) +
      (if C.turnRow ∈ Grid.cIco (x b) (x c) ∧
        C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x c) then 1 else 0)) +
      ((if C.oppositeTurnRow ∈ Grid.cIco (x b) (x a) ∧
        C.turnRow ∈ Grid.cIoo C.oppositeTurnRow (x a) then 1 else 0) +
      (if C.turnRow ∈ Grid.cIco (x c) (x b) ∧
        C.oppositeTurnRow ∈ Grid.cIoo C.turnRow (x b) then 1 else 0)) := by
  simp only [Finsupp.add_apply,
    G.unblockedDifferential_commutationHomotopy_single_apply C R,
    G.commutationHomotopy_unblockedDifferential_single_apply C R,
    G.sum_commutationHexagonCoefficient_mul_unblockedCoefficient C R,
    G.sum_unblockedCoefficient_mul_commutationHexagonCoefficient C R,
    G.sum_hexagonRectangleWeight_diagonal C R,
    G.sum_rectangleHexagonWeight_diagonal C R,
    G.card_hexagonRectangleDecompositions_diagonal C,
    G.card_rectangleHexagonDecompositions_diagonal C,
    Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end GridDiagram
end TauCeti
