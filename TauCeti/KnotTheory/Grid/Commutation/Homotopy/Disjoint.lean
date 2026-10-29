/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Disjoint
import Mathlib.Algebra.CharP.Two

/-!
# Cancelling disjoint hexagon--rectangle terms

In the commutation homotopy equation, a hexagon followed by a rectangle and a rectangle
followed by a hexagon contribute to the same coefficient. If the two pairs of vertical sides
are disjoint, the underlying rectangles can be applied in the opposite order. Their toroidal
domains are unchanged, so the hexagon retains both intersection rows and its turn-side kind.
Emptiness, `X`-avoidance and the `O`-monomial weight are preserved.

This gives a weight-preserving bijection for both kinds of commutation hexagon at once.
In characteristic two, the two disjoint-side sums cancel. Consequently the hexagon side
of the homotopy equation can be restricted to domains sharing a vertical side.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).

The reordering and emptiness proofs reuse the rectangle pairing in
`TauCeti.KnotTheory.Grid.Differential.Square.Disjoint`.
-/

public section

namespace TauCeti

namespace GridRectangleHexagonDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Apply a rectangle and a commutation hexagon in the opposite order when their vertical
side pairs are disjoint. -/
def commute (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    GridHexagonRectangleDecomposition a s s' x z where
  middle := (D.toRectangleDecomposition.commute h).middle
  first := GridCommutationHexagonBetween.ofToGridRectangleEq
    (D.toRectangleDecomposition.commute h).first D.second
    (D.toRectangleDecomposition.commute_first_toGridRectangle h)
  second := (D.toRectangleDecomposition.commute h).second

/-- Forgetting the turns after reordering agrees with rectangle reordering. -/
@[simp]
theorem commute_toRectangleDecomposition (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition = D.toRectangleDecomposition.commute h := by
  simp [commute, GridHexagonRectangleDecomposition.toRectangleDecomposition]

/-- The intermediate state after reordering is obtained by applying the hexagon first. -/
@[simp]
theorem commute_middle (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).middle =
      x.swapColumns D.second.toGridRectangleBetween.left D.second.toGridRectangleBetween.right := by
  exact (congrArg GridTwoStepDecomposition.middle (D.commute_toRectangleDecomposition h)).trans
    (D.toRectangleDecomposition.commute_middle h)

/-- Reordering preserves disjointness of the side pairs. -/
theorem hasDisjointSides_commute (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition.HasDisjointSides := by
  rw [D.commute_toRectangleDecomposition h]
  exact D.toRectangleDecomposition.hasDisjointSides_commute h

/-- Reordering preserves the squares covered by the hexagon. -/
@[simp]
theorem commute_hexagon_coveredSquares (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).first.coveredSquares = D.second.coveredSquares := by
  simp [commute]

/-- Reordering preserves the toroidal rectangle. -/
@[simp]
theorem commute_rectangle_toGridRectangle (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).second.toGridRectangle = D.first.toGridRectangle :=
  D.toRectangleDecomposition.commute_second_toGridRectangle h

end GridRectangleHexagonDecomposition

namespace GridHexagonRectangleDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Apply a commutation hexagon and a rectangle in the opposite order when their vertical
side pairs are disjoint. -/
def commute (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    GridRectangleHexagonDecomposition a s s' x z where
  middle := (D.toRectangleDecomposition.commute h).middle
  first := (D.toRectangleDecomposition.commute h).first
  second := GridCommutationHexagonBetween.ofToGridRectangleEq
    (D.toRectangleDecomposition.commute h).second D.first
    (D.toRectangleDecomposition.commute_second_toGridRectangle h)

/-- Forgetting the turns after reordering agrees with rectangle reordering. -/
@[simp]
theorem commute_toRectangleDecomposition (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition = D.toRectangleDecomposition.commute h := by
  simp [commute, GridRectangleHexagonDecomposition.toRectangleDecomposition]

/-- The intermediate state after reordering is obtained by applying the rectangle first. -/
@[simp]
theorem commute_middle (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).middle = x.swapColumns D.second.left D.second.right := by
  exact (congrArg GridTwoStepDecomposition.middle (D.commute_toRectangleDecomposition h)).trans
    (D.toRectangleDecomposition.commute_middle h)

/-- Reordering preserves disjointness of the side pairs. -/
theorem hasDisjointSides_commute (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).toRectangleDecomposition.HasDisjointSides := by
  rw [D.commute_toRectangleDecomposition h]
  exact D.toRectangleDecomposition.hasDisjointSides_commute h

/-- Reordering preserves the squares covered by the hexagon. -/
@[simp]
theorem commute_hexagon_coveredSquares (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).second.coveredSquares = D.first.coveredSquares := by
  simp [commute]

/-- Reordering preserves the toroidal rectangle. -/
@[simp]
theorem commute_rectangle_toGridRectangle (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).first.toGridRectangle = D.second.toGridRectangle :=
  D.toRectangleDecomposition.commute_first_toGridRectangle h

/-- Reordering a disjoint hexagon--rectangle domain twice recovers it. -/
@[simp]
theorem commute_commute (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  apply toRectangleDecomposition_injective
  simp only [GridRectangleHexagonDecomposition.commute_toRectangleDecomposition,
    commute_toRectangleDecomposition, GridRectangleDecomposition.commute_commute]

end GridHexagonRectangleDecomposition

namespace GridRectangleHexagonDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Reordering a disjoint rectangle--hexagon domain twice recovers it. -/
@[simp]
theorem commute_commute (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  apply toRectangleDecomposition_injective
  simp only [GridHexagonRectangleDecomposition.commute_toRectangleDecomposition,
    commute_toRectangleDecomposition, GridRectangleDecomposition.commute_commute]

end GridRectangleHexagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- Reordering a counted disjoint rectangle--hexagon domain gives a counted
hexagon--rectangle domain. -/
theorem commute_mem_hexagonRectangleDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z)
    (h : D.toRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.rectangleHexagonDecompositions C x z) :
    D.commute h ∈ G.hexagonRectangleDecompositions C x z := by
  obtain ⟨hr, hP⟩ := (G.mem_rectangleHexagonDecompositions C D).mp hD
  obtain ⟨hrEmpty, hrX⟩ := (G.mem_unblockedRectangles _).mp hr
  obtain ⟨hPEmpty, hPX⟩ := (G.mem_commutationHexagons C _).mp hP
  refine (G.mem_hexagonRectangleDecompositions C _).mpr ⟨?_, ?_⟩
  · refine (G.mem_commutationHexagons C _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_first h hrEmpty hPEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · simpa only [D.commute_hexagon_coveredSquares h] using hPX
  · refine (G.mem_unblockedRectangles _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_second h hrEmpty hPEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · simpa only [D.commute_rectangle_toGridRectangle h] using hrX

/-- Reordering a counted disjoint hexagon--rectangle domain gives a counted
rectangle--hexagon domain. -/
theorem commute_mem_rectangleHexagonDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z)
    (h : D.toRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.hexagonRectangleDecompositions C x z) :
    D.commute h ∈ G.rectangleHexagonDecompositions C x z := by
  obtain ⟨hP, hr⟩ := (G.mem_hexagonRectangleDecompositions C D).mp hD
  obtain ⟨hPEmpty, hPX⟩ := (G.mem_commutationHexagons C _).mp hP
  obtain ⟨hrEmpty, hrX⟩ := (G.mem_unblockedRectangles _).mp hr
  refine (G.mem_rectangleHexagonDecompositions C _).mpr ⟨?_, ?_⟩
  · refine (G.mem_unblockedRectangles _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_first h hPEmpty hrEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · simpa only [D.commute_rectangle_toGridRectangle h] using hrX
  · refine (G.mem_commutationHexagons C _).mpr ⟨?_, ?_⟩
    · have he := D.toRectangleDecomposition.isEmpty_commute_second h hPEmpty hrEmpty
      rw [← D.commute_toRectangleDecomposition h] at he
      exact he
    · simpa only [D.commute_hexagon_coveredSquares h] using hPX

variable (R : Type*) [CommSemiring R]

/-- Reordering a disjoint rectangle--hexagon domain preserves its monomial weight. -/
theorem hexagonRectangleWeight_commute_rectangleHexagon {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    G.hexagonRectangleWeight C R (D.commute h) = G.rectangleHexagonWeight C R D := by
  simp only [hexagonRectangleWeight_def, rectangleHexagonWeight_def,
    commutationHexagonWeight_eq_prod_coveredSquares,
    D.commute_hexagon_coveredSquares h, D.commute_rectangle_toGridRectangle h, mul_comm]

/-- Reordering a disjoint hexagon--rectangle domain preserves its monomial weight. -/
theorem rectangleHexagonWeight_commute_hexagonRectangle {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    G.rectangleHexagonWeight C R (D.commute h) = G.hexagonRectangleWeight C R D := by
  have hw := G.hexagonRectangleWeight_commute_rectangleHexagon C R (D.commute h)
    (D.hasDisjointSides_commute h)
  rw [D.commute_commute h] at hw
  exact hw.symm

open scoped Classical in
/-- The disjoint rectangle--hexagon and hexagon--rectangle contributions to the
commutation homotopy equation have the same total weight, for both hexagon kinds. -/
theorem sum_rectangleHexagonWeight_disjoint_eq_sum_hexagonRectangleWeight_disjoint
    (x z : GridState n) :
    ∑ D ∈ (G.rectangleHexagonDecompositions C x z).filter
        (fun D => D.toRectangleDecomposition.HasDisjointSides), G.rectangleHexagonWeight C R D =
      ∑ D ∈ (G.hexagonRectangleDecompositions C x z).filter
        (fun D => D.toRectangleDecomposition.HasDisjointSides), G.hexagonRectangleWeight C R D := by
  refine Finset.sum_bij'
    (fun D hD => D.commute (Finset.mem_filter.mp hD).2)
    (fun E hE => E.commute (Finset.mem_filter.mp hE).2) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    obtain ⟨hD, h⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr
      ⟨G.commute_mem_hexagonRectangleDecompositions C D h hD, D.hasDisjointSides_commute h⟩
  · intro E hE
    obtain ⟨hE, h⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr
      ⟨G.commute_mem_rectangleHexagonDecompositions C E h hE, E.hasDisjointSides_commute h⟩
  · intro D hD
    exact D.commute_commute (Finset.mem_filter.mp hD).2
  · intro E hE
    exact E.commute_commute (Finset.mem_filter.mp hE).2
  · intro D hD
    exact (G.hexagonRectangleWeight_commute_rectangleHexagon C R D
      (Finset.mem_filter.mp hD).2).symm

variable [CharP R 2]

open scoped Classical in
/-- In characteristic two, only hexagon--rectangle domains sharing a side contribute to
the left-hand side of the commutation homotopy equation. -/
theorem sum_hexagonRectangleWeight_add_sum_rectangleHexagonWeight_eq_overlap
    (x z : GridState n) :
    (∑ D ∈ G.hexagonRectangleDecompositions C x z, G.hexagonRectangleWeight C R D) +
        ∑ D ∈ G.rectangleHexagonDecompositions C x z, G.rectangleHexagonWeight C R D =
      (∑ D ∈ (G.hexagonRectangleDecompositions C x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.hexagonRectangleWeight C R D) +
      ∑ D ∈ (G.rectangleHexagonDecompositions C x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.rectangleHexagonWeight C R D := by
  rw [← Finset.sum_filter_add_sum_filter_not (G.hexagonRectangleDecompositions C x z)
      (fun D => D.toRectangleDecomposition.HasDisjointSides),
    ← Finset.sum_filter_add_sum_filter_not (G.rectangleHexagonDecompositions C x z)
      (fun D => D.toRectangleDecomposition.HasDisjointSides),
    G.sum_rectangleHexagonWeight_disjoint_eq_sum_hexagonRectangleWeight_disjoint C R x z,
    add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]

open scoped Classical in
/-- In characteristic two, the commutation homotopy equation is equivalent to the
coefficient identity restricted to hexagon--rectangle domains sharing a vertical side. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff_overlap :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns C.column (finRotate n C.column)).commutationMap R C.reverse
          (G.commutationMap R C c)) ↔
      ∀ x z : GridState n,
        (∑ D ∈ (G.hexagonRectangleDecompositions C x z).filter
            (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.hexagonRectangleWeight C R D) +
          ∑ D ∈ (G.rectangleHexagonDecompositions C x z).filter
              (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
            G.rectangleHexagonWeight C R D =
          (if x = z then 1 else 0) +
            ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  rw [G.unblockedDifferential_commutationHomotopy_add_eq_iff_decompositions C R]
  simp_rw [G.sum_hexagonRectangleWeight_add_sum_rectangleHexagonWeight_eq_overlap C R]

end GridDiagram

end TauCeti
