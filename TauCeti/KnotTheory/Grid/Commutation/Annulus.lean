/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.KnotTheory.Grid.Rectangle.Annulus
public import TauCeti.KnotTheory.Grid.Commutation.Decomposition

/-!
# Annular orientations in the pentagon chain-map equation

The diagonal coefficient of the grid-commutation chain-map equation counts a rectangle and a
pentagon whose straightening returns to the source grid state. The two straightened rectangles
therefore have the same unordered side columns. There are exactly two possibilities: their
ordered side columns agree, or they occur in opposite orders.

This file makes that dichotomy exact for both orders of composition. It partitions each finite
set of diagonal rectangle--pentagon decompositions into same-order and opposite-order terms, and
splits every weighted sum along that partition. These are the two annular orientations that must
be treated separately in the exceptional diagonal case of the commutation chain-map proof.

## Main definitions

* `TauCeti.GridDiagram.rectanglePentagonSameSideOrder` and
  `TauCeti.GridDiagram.rectanglePentagonOppositeSideOrder`: the two orientations when the
  rectangle precedes the pentagon.
* `TauCeti.GridDiagram.pentagonRectangleSameSideOrder` and
  `TauCeti.GridDiagram.pentagonRectangleOppositeSideOrder`: the corresponding orientations when
  the pentagon precedes the rectangle.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.side_order_cases_of_diagonal` and
  `TauCeti.GridPentagonRectangleDecomposition.side_order_cases_of_diagonal`: a returning
  decomposition has one of the two side orders.
* The covered-square union lemmas: the two side orders give a vertical or horizontal annulus.
* `TauCeti.GridDiagram.rectanglePentagonSameSideOrder_union_oppositeSideOrder` and
  `TauCeti.GridDiagram.pentagonRectangleSameSideOrder_union_oppositeSideOrder`: the two families
  exhaust the corresponding diagonal decomposition set.
* `TauCeti.GridDiagram.sum_rectanglePentagonDecompositions_self` and
  `TauCeti.GridDiagram.sum_pentagonRectangleDecompositions_self`: every weighted diagonal sum
  splits into its two annular orientations.

## References

The split is Case (P-3) in Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*,
Section 5.1, especially Figures 5.5 and 5.6.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- A rectangle followed by a pentagon and returning to its source has either the same ordered
side columns as the pentagon or the opposite ordered side columns. -/
theorem side_order_cases_of_diagonal (D : GridRectanglePentagonDecomposition a s x x) :
    (D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right) ∨
      (D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left) := by
  rcases D.rectangle.left_right_eq_cases D.pentagon.toGridRectangleBetween with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

/-- The two side-order alternatives for a diagonal rectangle--pentagon decomposition are
mutually exclusive. -/
theorem not_same_and_opposite_side_order (D : GridRectanglePentagonDecomposition a s x x) :
    ¬((D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right) ∧
      (D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left)) := by
  rintro ⟨hsame, hopposite⟩
  exact D.rectangle.left_ne_right (hsame.1.trans hopposite.2.symm)

/-- In the same-side-order case, the two straightened rectangles cover a vertical annulus. -/
theorem coveredSquares_union_eq_product_univ_of_same_side_order
    (D : GridRectanglePentagonDecomposition a s x x)
    (h : D.rectangle.left = D.pentagon.left ∧
      D.rectangle.right = D.pentagon.right) :
    D.rectangle.toGridRectangle.coveredSquares ∪
        D.pentagon.toGridRectangle.coveredSquares =
      D.rectangle.toGridRectangle.coveredColumns ×ˢ (Finset.univ : Finset (Fin n)) := by
  exact D.rectangle.coveredSquares_union_coveredSquares_of_left_eq_left
    D.pentagon.toGridRectangleBetween h.1.symm

/-- In the opposite-side-order case, the two straightened rectangles cover a horizontal
annulus. -/
theorem coveredSquares_union_eq_univ_product_of_opposite_side_order
    (D : GridRectanglePentagonDecomposition a s x x)
    (h : D.rectangle.left = D.pentagon.right ∧
      D.rectangle.right = D.pentagon.left) :
    D.rectangle.toGridRectangle.coveredSquares ∪
        D.pentagon.toGridRectangle.coveredSquares =
      (Finset.univ : Finset (Fin n)) ×ˢ D.rectangle.toGridRectangle.coveredRows := by
  exact D.rectangle.coveredSquares_union_coveredSquares_of_left_eq_right
    D.pentagon.toGridRectangleBetween h.2.symm

end GridRectanglePentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- A pentagon followed by a rectangle and returning to its source has either the same ordered
side columns as the pentagon or the opposite ordered side columns. -/
theorem side_order_cases_of_diagonal (D : GridPentagonRectangleDecomposition a s x x) :
    (D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right) ∨
      (D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left) := by
  exact D.pentagon.toGridRectangleBetween.left_right_eq_cases D.rectangle

/-- The two side-order alternatives for a diagonal pentagon--rectangle decomposition are
mutually exclusive. -/
theorem not_same_and_opposite_side_order (D : GridPentagonRectangleDecomposition a s x x) :
    ¬((D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right) ∧
      (D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left)) := by
  rintro ⟨hsame, hopposite⟩
  exact D.rectangle.left_ne_right (hsame.1.trans hopposite.2.symm)

/-- In the same-side-order case, the two straightened rectangles cover a vertical annulus. -/
theorem coveredSquares_union_eq_product_univ_of_same_side_order
    (D : GridPentagonRectangleDecomposition a s x x)
    (h : D.rectangle.left = D.pentagon.left ∧
      D.rectangle.right = D.pentagon.right) :
    D.pentagon.toGridRectangle.coveredSquares ∪
        D.rectangle.toGridRectangle.coveredSquares =
      D.pentagon.toGridRectangle.coveredColumns ×ˢ (Finset.univ : Finset (Fin n)) := by
  exact D.pentagon.toGridRectangleBetween.coveredSquares_union_coveredSquares_of_left_eq_left
    D.rectangle h.1

/-- In the opposite-side-order case, the two straightened rectangles cover a horizontal
annulus. -/
theorem coveredSquares_union_eq_univ_product_of_opposite_side_order
    (D : GridPentagonRectangleDecomposition a s x x)
    (h : D.rectangle.left = D.pentagon.right ∧
      D.rectangle.right = D.pentagon.left) :
    D.pentagon.toGridRectangle.coveredSquares ∪
        D.rectangle.toGridRectangle.coveredSquares =
      (Finset.univ : Finset (Fin n)) ×ˢ D.pentagon.toGridRectangle.coveredRows := by
  exact D.pentagon.toGridRectangleBetween.coveredSquares_union_coveredSquares_of_left_eq_right
    D.rectangle h.1

end GridPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- The diagonal rectangle--pentagon terms whose rectangle and pentagon have the same ordered
side columns. -/
noncomputable def rectanglePentagonSameSideOrder (x : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x x) :=
  (G.rectanglePentagonDecompositions C x x).filter fun D =>
    D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right

/-- The diagonal rectangle--pentagon terms whose rectangle and pentagon have opposite ordered
side columns. -/
noncomputable def rectanglePentagonOppositeSideOrder (x : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x x) :=
  (G.rectanglePentagonDecompositions C x x).filter fun D =>
    D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left

/-- Membership in the same-side-order rectangle--pentagon family. -/
@[simp]
theorem mem_rectanglePentagonSameSideOrder (x : GridState n)
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x) :
    D ∈ G.rectanglePentagonSameSideOrder C x ↔
      D ∈ G.rectanglePentagonDecompositions C x x ∧
        D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right := by
  simp [rectanglePentagonSameSideOrder]

/-- Membership in the opposite-side-order rectangle--pentagon family. -/
@[simp]
theorem mem_rectanglePentagonOppositeSideOrder (x : GridState n)
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x) :
    D ∈ G.rectanglePentagonOppositeSideOrder C x ↔
      D ∈ G.rectanglePentagonDecompositions C x x ∧
        D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left := by
  simp [rectanglePentagonOppositeSideOrder]

/-- The same- and opposite-side-order rectangle--pentagon families are disjoint. -/
theorem disjoint_rectanglePentagonSameSideOrder_oppositeSideOrder (x : GridState n) :
    Disjoint (G.rectanglePentagonSameSideOrder C x)
      (G.rectanglePentagonOppositeSideOrder C x) := by
  rw [Finset.disjoint_left]
  intro D hsame hopposite
  exact D.not_same_and_opposite_side_order
    ⟨((G.mem_rectanglePentagonSameSideOrder C x D).1 hsame).2,
      ((G.mem_rectanglePentagonOppositeSideOrder C x D).1 hopposite).2⟩

open Classical in
/-- The same- and opposite-side-order families exhaust all diagonal rectangle--pentagon terms. -/
theorem rectanglePentagonSameSideOrder_union_oppositeSideOrder (x : GridState n) :
    G.rectanglePentagonSameSideOrder C x ∪ G.rectanglePentagonOppositeSideOrder C x =
      G.rectanglePentagonDecompositions C x x := by
  ext D
  simp only [Finset.mem_union, mem_rectanglePentagonSameSideOrder,
    mem_rectanglePentagonOppositeSideOrder]
  constructor
  · rintro (⟨hD, -⟩ | ⟨hD, -⟩) <;> exact hD
  · intro hD
    exact (D.side_order_cases_of_diagonal.elim (fun h => Or.inl ⟨hD, h⟩)
      fun h => Or.inr ⟨hD, h⟩)

/-- The diagonal pentagon--rectangle terms whose rectangle and pentagon have the same ordered
side columns. -/
noncomputable def pentagonRectangleSameSideOrder (x : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x x) :=
  (G.pentagonRectangleDecompositions C x x).filter fun D =>
    D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right

/-- The diagonal pentagon--rectangle terms whose rectangle and pentagon have opposite ordered
side columns. -/
noncomputable def pentagonRectangleOppositeSideOrder (x : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x x) :=
  (G.pentagonRectangleDecompositions C x x).filter fun D =>
    D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left

/-- Membership in the same-side-order pentagon--rectangle family. -/
@[simp]
theorem mem_pentagonRectangleSameSideOrder (x : GridState n)
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x) :
    D ∈ G.pentagonRectangleSameSideOrder C x ↔
      D ∈ G.pentagonRectangleDecompositions C x x ∧
        D.rectangle.left = D.pentagon.left ∧ D.rectangle.right = D.pentagon.right := by
  simp [pentagonRectangleSameSideOrder]

/-- Membership in the opposite-side-order pentagon--rectangle family. -/
@[simp]
theorem mem_pentagonRectangleOppositeSideOrder (x : GridState n)
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x) :
    D ∈ G.pentagonRectangleOppositeSideOrder C x ↔
      D ∈ G.pentagonRectangleDecompositions C x x ∧
        D.rectangle.left = D.pentagon.right ∧ D.rectangle.right = D.pentagon.left := by
  simp [pentagonRectangleOppositeSideOrder]

/-- The same- and opposite-side-order pentagon--rectangle families are disjoint. -/
theorem disjoint_pentagonRectangleSameSideOrder_oppositeSideOrder (x : GridState n) :
    Disjoint (G.pentagonRectangleSameSideOrder C x)
      (G.pentagonRectangleOppositeSideOrder C x) := by
  rw [Finset.disjoint_left]
  intro D hsame hopposite
  exact D.not_same_and_opposite_side_order
    ⟨((G.mem_pentagonRectangleSameSideOrder C x D).1 hsame).2,
      ((G.mem_pentagonRectangleOppositeSideOrder C x D).1 hopposite).2⟩

open Classical in
/-- The same- and opposite-side-order families exhaust all diagonal pentagon--rectangle terms. -/
theorem pentagonRectangleSameSideOrder_union_oppositeSideOrder (x : GridState n) :
    G.pentagonRectangleSameSideOrder C x ∪ G.pentagonRectangleOppositeSideOrder C x =
      G.pentagonRectangleDecompositions C x x := by
  ext D
  simp only [Finset.mem_union, mem_pentagonRectangleSameSideOrder,
    mem_pentagonRectangleOppositeSideOrder]
  constructor
  · rintro (⟨hD, -⟩ | ⟨hD, -⟩) <;> exact hD
  · intro hD
    exact (D.side_order_cases_of_diagonal.elim (fun h => Or.inl ⟨hD, h⟩)
      fun h => Or.inr ⟨hD, h⟩)

open Classical in
/-- A weighted sum over diagonal rectangle--pentagon terms splits into the two annular side
orientations. -/
theorem sum_rectanglePentagonDecompositions_self {M : Type*} [AddCommMonoid M]
    (x : GridState n) (w : GridRectanglePentagonDecomposition C.column C.turnRow x x → M) :
    ∑ D ∈ G.rectanglePentagonDecompositions C x x, w D =
      (∑ D ∈ G.rectanglePentagonSameSideOrder C x, w D) +
        ∑ D ∈ G.rectanglePentagonOppositeSideOrder C x, w D := by
  rw [← G.rectanglePentagonSameSideOrder_union_oppositeSideOrder C x,
    Finset.sum_union (G.disjoint_rectanglePentagonSameSideOrder_oppositeSideOrder C x)]

open Classical in
/-- A weighted sum over diagonal pentagon--rectangle terms splits into the two annular side
orientations. -/
theorem sum_pentagonRectangleDecompositions_self {M : Type*} [AddCommMonoid M]
    (x : GridState n) (w : GridPentagonRectangleDecomposition C.column C.turnRow x x → M) :
    ∑ D ∈ G.pentagonRectangleDecompositions C x x, w D =
      (∑ D ∈ G.pentagonRectangleSameSideOrder C x, w D) +
        ∑ D ∈ G.pentagonRectangleOppositeSideOrder C x, w D := by
  rw [← G.pentagonRectangleSameSideOrder_union_oppositeSideOrder C x,
    Finset.sum_union (G.disjoint_pentagonRectangleSameSideOrder_oppositeSideOrder C x)]

end GridDiagram

end TauCeti
