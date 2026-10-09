/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Basic
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition

/-!
# Annular orientations for initial-side pentagons

The diagonal terms contributed by the initial-side pentagons in the grid-commutation chain-map
equation are returning pairs of rectangles after forgetting the distinguished turn point. Their
two ordered pairs of side columns therefore either agree or occur in opposite orders. These are
the vertical and horizontal annular orientations.

This file records that dichotomy for both composition orders, partitions the two finite families
of counted diagonal terms, and splits their weighted sums. It is the initial-side counterpart of
`TauCeti.KnotTheory.Grid.Commutation.Annulus.Basic`; the geometric thinness forced by emptiness is
developed in `TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Empty`.

## Main definitions

* `TauCeti.GridDiagram.rectangleInitialPentagonSameSideOrder` and
  `TauCeti.GridDiagram.rectangleInitialPentagonOppositeSideOrder`: the two orientations when a
  rectangle precedes an initial-side pentagon.
* `TauCeti.GridDiagram.initialPentagonRectangleSameSideOrder` and
  `TauCeti.GridDiagram.initialPentagonRectangleOppositeSideOrder`: the corresponding orientations
  in the opposite composition order.

## Main results

* `TauCeti.GridDiagram.rectangleInitialPentagonSameSideOrder_union_oppositeSideOrder` and
  `TauCeti.GridDiagram.initialPentagonRectangleSameSideOrder_union_oppositeSideOrder`: each pair
  of families exhausts the relevant diagonal terms.
* `TauCeti.GridDiagram.sum_rectangleInitialPentagonDecompositions_self` and
  `TauCeti.GridDiagram.sum_initialPentagonRectangleDecompositions_self`: the corresponding
  weighted sums split along the two annular orientations.

## References

This is the initial-side part of Case (P-3) in Ozsvath--Stipsicz--Szabo,
*Grid Homology for Knots and Links*, Section 5.1, especially Figures 5.5 and 5.6.
-/

public section

namespace TauCeti

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The same- and opposite-side-order alternatives for a rectangle followed by an initial-side
pentagon are mutually exclusive. -/
theorem not_same_and_opposite_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x z) :
    ¬((D.first.left = D.second.left ∧ D.first.right = D.second.right) ∧
      (D.first.left = D.second.right ∧ D.first.right = D.second.left)) := by
  rintro ⟨hsame, hopposite⟩
  exact D.first.left_ne_right (hsame.1.trans hopposite.2.symm)

end GridRectangleInitialPentagonDecomposition

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The same- and opposite-side-order alternatives for an initial-side pentagon followed by a
rectangle are mutually exclusive. -/
theorem not_same_and_opposite_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x z) :
    ¬((D.second.left = D.first.left ∧ D.second.right = D.first.right) ∧
      (D.second.left = D.first.right ∧ D.second.right = D.first.left)) := by
  rintro ⟨hsame, hopposite⟩
  exact D.second.left_ne_right (hsame.1.trans hopposite.2.symm)

end GridInitialPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- The diagonal rectangle--initial-side pentagon terms whose two rectangles have the same
ordered side columns. -/
noncomputable def rectangleInitialPentagonSameSideOrder (x : GridState n) :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x x) :=
  (G.rectangleInitialPentagonDecompositions C x x).filter fun D =>
    D.first.left = D.second.left ∧ D.first.right = D.second.right

/-- The diagonal rectangle--initial-side pentagon terms whose two rectangles have opposite
ordered side columns. -/
noncomputable def rectangleInitialPentagonOppositeSideOrder (x : GridState n) :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x x) :=
  (G.rectangleInitialPentagonDecompositions C x x).filter fun D =>
    D.first.left = D.second.right ∧ D.first.right = D.second.left

/-- Membership in the same-side-order rectangle--initial-side pentagon family. -/
@[simp]
theorem mem_rectangleInitialPentagonSameSideOrder (x : GridState n)
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x) :
    D ∈ G.rectangleInitialPentagonSameSideOrder C x ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x x ∧
        D.first.left = D.second.left ∧ D.first.right = D.second.right := by
  simp [rectangleInitialPentagonSameSideOrder]

/-- Membership in the opposite-side-order rectangle--initial-side pentagon family. -/
@[simp]
theorem mem_rectangleInitialPentagonOppositeSideOrder (x : GridState n)
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x) :
    D ∈ G.rectangleInitialPentagonOppositeSideOrder C x ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x x ∧
        D.first.left = D.second.right ∧ D.first.right = D.second.left := by
  simp [rectangleInitialPentagonOppositeSideOrder]

/-- The same- and opposite-side-order rectangle--initial-side pentagon families are disjoint. -/
theorem disjoint_rectangleInitialPentagonSameSideOrder_oppositeSideOrder (x : GridState n) :
    Disjoint (G.rectangleInitialPentagonSameSideOrder C x)
      (G.rectangleInitialPentagonOppositeSideOrder C x) := by
  rw [Finset.disjoint_left]
  intro D hsame hopposite
  exact D.not_same_and_opposite_side_order
    ⟨((G.mem_rectangleInitialPentagonSameSideOrder C x D).1 hsame).2,
      ((G.mem_rectangleInitialPentagonOppositeSideOrder C x D).1 hopposite).2⟩

open Classical in
/-- The same- and opposite-side-order families exhaust all diagonal rectangle--initial-side
pentagon terms. -/
theorem rectangleInitialPentagonSameSideOrder_union_oppositeSideOrder (x : GridState n) :
    G.rectangleInitialPentagonSameSideOrder C x ∪
        G.rectangleInitialPentagonOppositeSideOrder C x =
      G.rectangleInitialPentagonDecompositions C x x := by
  ext D
  simp only [Finset.mem_union, mem_rectangleInitialPentagonSameSideOrder,
    mem_rectangleInitialPentagonOppositeSideOrder]
  constructor
  · rintro (⟨hD, -⟩ | ⟨hD, -⟩) <;> exact hD
  · intro hD
    rcases D.first.left_right_eq_cases D.second with h | h
    · exact Or.inl ⟨hD, h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨hD, h.2.symm, h.1.symm⟩

/-- The diagonal initial-side pentagon--rectangle terms whose two rectangles have the same
ordered side columns. -/
noncomputable def initialPentagonRectangleSameSideOrder (x : GridState n) :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x x) :=
  (G.initialPentagonRectangleDecompositions C x x).filter fun D =>
    D.second.left = D.first.left ∧ D.second.right = D.first.right

/-- The diagonal initial-side pentagon--rectangle terms whose two rectangles have opposite
ordered side columns. -/
noncomputable def initialPentagonRectangleOppositeSideOrder (x : GridState n) :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x x) :=
  (G.initialPentagonRectangleDecompositions C x x).filter fun D =>
    D.second.left = D.first.right ∧ D.second.right = D.first.left

/-- Membership in the same-side-order initial-side pentagon--rectangle family. -/
@[simp]
theorem mem_initialPentagonRectangleSameSideOrder (x : GridState n)
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x) :
    D ∈ G.initialPentagonRectangleSameSideOrder C x ↔
      D ∈ G.initialPentagonRectangleDecompositions C x x ∧
        D.second.left = D.first.left ∧ D.second.right = D.first.right := by
  simp [initialPentagonRectangleSameSideOrder]

/-- Membership in the opposite-side-order initial-side pentagon--rectangle family. -/
@[simp]
theorem mem_initialPentagonRectangleOppositeSideOrder (x : GridState n)
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x) :
    D ∈ G.initialPentagonRectangleOppositeSideOrder C x ↔
      D ∈ G.initialPentagonRectangleDecompositions C x x ∧
        D.second.left = D.first.right ∧ D.second.right = D.first.left := by
  simp [initialPentagonRectangleOppositeSideOrder]

/-- The same- and opposite-side-order initial-side pentagon--rectangle families are disjoint. -/
theorem disjoint_initialPentagonRectangleSameSideOrder_oppositeSideOrder (x : GridState n) :
    Disjoint (G.initialPentagonRectangleSameSideOrder C x)
      (G.initialPentagonRectangleOppositeSideOrder C x) := by
  rw [Finset.disjoint_left]
  intro D hsame hopposite
  exact D.not_same_and_opposite_side_order
    ⟨((G.mem_initialPentagonRectangleSameSideOrder C x D).1 hsame).2,
      ((G.mem_initialPentagonRectangleOppositeSideOrder C x D).1 hopposite).2⟩

open Classical in
/-- The same- and opposite-side-order families exhaust all diagonal initial-side
pentagon--rectangle terms. -/
theorem initialPentagonRectangleSameSideOrder_union_oppositeSideOrder (x : GridState n) :
    G.initialPentagonRectangleSameSideOrder C x ∪
        G.initialPentagonRectangleOppositeSideOrder C x =
      G.initialPentagonRectangleDecompositions C x x := by
  ext D
  simp only [Finset.mem_union, mem_initialPentagonRectangleSameSideOrder,
    mem_initialPentagonRectangleOppositeSideOrder]
  constructor
  · rintro (⟨hD, -⟩ | ⟨hD, -⟩) <;> exact hD
  · intro hD
    exact (D.first.left_right_eq_cases D.second).elim
      (fun h => Or.inl ⟨hD, h⟩) fun h => Or.inr ⟨hD, h⟩

open Classical in
/-- A weighted sum over diagonal rectangle--initial-side pentagon terms splits into the two
annular side orientations. -/
theorem sum_rectangleInitialPentagonDecompositions_self {M : Type*} [AddCommMonoid M]
    (x : GridState n) (w : GridRectangleInitialPentagonDecomposition
      C.column C.turnRow x x → M) :
    ∑ D ∈ G.rectangleInitialPentagonDecompositions C x x, w D =
      (∑ D ∈ G.rectangleInitialPentagonSameSideOrder C x, w D) +
        ∑ D ∈ G.rectangleInitialPentagonOppositeSideOrder C x, w D := by
  rw [← G.rectangleInitialPentagonSameSideOrder_union_oppositeSideOrder C x,
    Finset.sum_union
      (G.disjoint_rectangleInitialPentagonSameSideOrder_oppositeSideOrder C x)]

open Classical in
/-- A weighted sum over diagonal initial-side pentagon--rectangle terms splits into the two
annular side orientations. -/
theorem sum_initialPentagonRectangleDecompositions_self {M : Type*} [AddCommMonoid M]
    (x : GridState n) (w : GridInitialPentagonRectangleDecomposition
      C.column C.turnRow x x → M) :
    ∑ D ∈ G.initialPentagonRectangleDecompositions C x x, w D =
      (∑ D ∈ G.initialPentagonRectangleSameSideOrder C x, w D) +
        ∑ D ∈ G.initialPentagonRectangleOppositeSideOrder C x, w D := by
  rw [← G.initialPentagonRectangleSameSideOrder_union_oppositeSideOrder C x,
    Finset.sum_union
      (G.disjoint_initialPentagonRectangleSameSideOrder_oppositeSideOrder C x)]

end GridDiagram

end TauCeti
