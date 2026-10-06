/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Empty

/-!
# X-markings in horizontal commutation annuli

A thin horizontal rectangle--pentagon annulus occupies the turn row, with precisely the
first commuted column missing. In the opposite composition order, the rectangle is read
in the commuted diagram, so its columns must be swapped back before testing markings.
The missing column is then the second commuted column. Consequently the two domains avoid
all X-markings exactly when the X-marking in the turn row lies in that missing column.

These exact marking tests identify which horizontal terms can contribute to the diagonal
coefficient of the pentagon chain-map equation. In particular, the two horizontal families
cannot both contribute, since X-markings occupy distinct rows in distinct columns.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6.
-/

public section

namespace TauCeti

namespace GridPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- Swapping the two commuted columns preserves a thin horizontal pentagon's covered squares,
since neither of those columns is covered. -/
private theorem coveredSquares_map_swap_eq_of_top_eq_finRotate_bottom
    (P : GridPentagonBetween a s x y) (hthin : P.top = finRotate n P.bottom) :
    P.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      P.coveredSquares := by
  classical
  rw [P.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom hthin]
  ext p
  simp only [Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    Finset.mem_product, Finset.mem_erase, Finset.mem_singleton]
  have hbnot := Grid.right_notMem_cIco P.left (finRotate n a)
  by_cases ha : p.1 = a
  · simp only [ha, Equiv.swap_apply_left, hbnot, and_false, false_and,
      ne_eq, not_true_eq_false]
  · by_cases hb : p.1 = finRotate n a
    · simp only [hb, Equiv.swap_apply_right, hbnot, and_false, false_and,
        ne_eq, not_true_eq_false]
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A thin pentagon together with a rectangle occupying its complementary column arc
covers the turn row except for the first commuted column. -/
theorem coveredSquares_union_of_opposite_side_order (P : GridPentagonBetween a s x y)
    (r : GridRectangle n) (hthin : P.top = finRotate n P.bottom)
    (hleft : r.left = finRotate n a) (hright : r.right = P.left)
    (hbottom : r.bottom = P.bottom) (htop : r.top = P.top) :
    P.coveredSquares ∪ r.coveredSquares = (Finset.univ.erase a) ×ˢ {s} := by
  rw [P.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom hthin]
  have hrows := P.cIco_bottom_top_eq_singleton_of_top_eq_finRotate_bottom hthin
  have hcols := Grid.cIco_union_swap P.left_ne
  have hnot : a ∉ Grid.cIco (finRotate n a) P.left := by simp
  ext p
  simp only [Finset.mem_union, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    hleft, hright, hbottom, htop, hrows, Finset.mem_product,
    Finset.mem_erase, Finset.mem_univ, Finset.mem_singleton, and_true]
  have hp : p.1 ∈ Grid.cIco P.left (finRotate n a) ∨
      p.1 ∈ Grid.cIco (finRotate n a) P.left := by
    rw [← Finset.mem_union, hcols]
    exact Finset.mem_univ _
  grind

/-- A thin horizontal pentagon and a rectangle on its complementary column arc cover
disjoint squares, regardless of the rectangle's row span. -/
theorem disjoint_coveredSquares_of_opposite_side_order (P : GridPentagonBetween a s x y)
    (r : GridRectangle n) (hthin : P.top = finRotate n P.bottom)
    (hleft : r.left = finRotate n a) (hright : r.right = P.left) :
    Disjoint P.coveredSquares r.coveredSquares := by
  rw [P.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom hthin,
    GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def, hleft, hright]
  exact Finset.disjoint_product.2 (Or.inl
    ((Grid.disjoint_cIco_swap P.left (finRotate n a)).mono_left (Finset.erase_subset _ _)))

end GridPentagonBetween

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- A thin horizontal rectangle--pentagon annulus covers the turn row except for the
first commuted column. This is a statement about markings, not interior grid points. -/
theorem coveredSquares_union_of_opposite_side_order
    (D : GridRectanglePentagonDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.rectangle.top = finRotate n D.rectangle.bottom) :
    D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.coveredSquares =
      (Finset.univ.erase a) ×ˢ {s} := by
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.rectangle hleft
  have hbottom := D.rectangle.bottom_eq_bottom_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  have htop := D.rectangle.top_eq_top_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  rw [Finset.union_comm]
  exact D.pentagon.coveredSquares_union_of_opposite_side_order D.rectangle.toGridRectangle
    (htop.trans (hthin.trans (congrArg (finRotate n) hbottom).symm))
    (hleft.trans D.pentagon.right_eq) hright hbottom.symm htop.symm

/-- The constituent domains of a thin horizontal rectangle--pentagon annulus cover disjoint
squares. -/
theorem disjoint_coveredSquares_of_opposite_side_order
    (D : GridRectanglePentagonDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.rectangle.top = finRotate n D.rectangle.bottom) :
    Disjoint D.rectangle.toGridRectangle.coveredSquares D.pentagon.coveredSquares := by
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.rectangle hleft
  have htop := D.rectangle.top_eq_top_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  have hbottom := D.rectangle.bottom_eq_bottom_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  have hPthin := htop.trans (hthin.trans (congrArg (finRotate n) hbottom).symm)
  exact (D.pentagon.disjoint_coveredSquares_of_opposite_side_order
    D.rectangle.toGridRectangle hPthin (hleft.trans D.pentagon.right_eq) hright).symm

/-- The two domains of a thin horizontal rectangle--pentagon annulus avoid X-markings
exactly when the first commuted column contains the X-marking in the turn row. -/
theorem disjoint_XSet_iff_X_column_eq_turnRow_of_opposite_side_order
    (D : GridRectanglePentagonDecomposition a s x x) (G : GridDiagram n)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.rectangle.top = finRotate n D.rectangle.bottom) :
    Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet ∧
        Disjoint D.pentagon.coveredSquares G.XSet ↔ G.X a = s := by
  rw [← Finset.disjoint_union_left,
    D.coveredSquares_union_of_opposite_side_order hleft hthin]
  exact G.X.disjoint_univ_erase_product_singleton_pointSet_iff a s

end GridRectanglePentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- Reading the rectangle of a thin horizontal pentagon--rectangle annulus back in the
original columns gives the turn row except for the second commuted column. -/
theorem coveredSquares_union_map_of_opposite_side_order
    (D : GridPentagonRectangleDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.pentagon.top = finRotate n D.pentagon.bottom) :
    D.pentagon.coveredSquares ∪ D.rectangle.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      (Finset.univ.erase (finRotate n a)) ×ˢ {s} := by
  classical
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.rectangle hleft
  have hbottom := D.pentagon.toGridRectangleBetween.bottom_eq_bottom_of_left_eq_right
    D.rectangle hleft
  have htop := D.pentagon.toGridRectangleBetween.top_eq_top_of_left_eq_right
    D.rectangle hleft
  let e := ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding
  have hunion := congrArg (fun S : Finset (Fin n × Fin n) => S.map e)
    (D.pentagon.coveredSquares_union_of_opposite_side_order D.rectangle.toGridRectangle
      hthin (hleft.trans D.pentagon.right_eq) hright hbottom htop)
  rw [Finset.map_union,
    D.pentagon.coveredSquares_map_swap_eq_of_top_eq_finRotate_bottom hthin] at hunion
  rw [hunion]
  -- Swapping back moves the missing square from the first column to the second.
  ext p
  simp only [e, Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    Finset.mem_product, Finset.mem_erase, Finset.mem_univ, Finset.mem_singleton, and_true,
    ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

/-- The pentagon and the rectangle read back in the original columns cover disjoint squares
in a thin horizontal pentagon--rectangle annulus. -/
theorem disjoint_coveredSquares_map_of_opposite_side_order
    (D : GridPentagonRectangleDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.pentagon.top = finRotate n D.pentagon.bottom) :
    Disjoint D.pentagon.coveredSquares (D.rectangle.toGridRectangle.coveredSquares.map
      ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding) := by
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.rectangle hleft
  let e := ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding
  have hdisjoint := D.pentagon.disjoint_coveredSquares_of_opposite_side_order
    D.rectangle.toGridRectangle hthin (hleft.trans D.pentagon.right_eq) hright
  have h := (Finset.disjoint_map e).2 hdisjoint
  rwa [D.pentagon.coveredSquares_map_swap_eq_of_top_eq_finRotate_bottom hthin] at h

/-- For a thin horizontal pentagon--rectangle annulus, with the rectangle tested against
the commuted diagram, X-avoidance is equivalent to the second commuted column containing
the X-marking in the turn row. -/
theorem disjoint_XSet_swapColumns_iff_X_next_eq_turnRow_of_opposite_side_order
    (D : GridPentagonRectangleDecomposition a s x x) (G : GridDiagram n)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hthin : D.pentagon.top = finRotate n D.pentagon.bottom) :
    Disjoint D.pentagon.coveredSquares G.XSet ∧
        Disjoint D.rectangle.toGridRectangle.coveredSquares
          (G.swapColumns a (finRotate n a)).XSet ↔ G.X (finRotate n a) = s := by
  rw [← G.disjoint_map_swapColumns_XSet_iff a (finRotate n a),
    ← Finset.disjoint_union_left,
    D.coveredSquares_union_map_of_opposite_side_order hleft hthin]
  exact G.X.disjoint_univ_erase_product_singleton_pointSet_iff (finRotate n a) s

end GridPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- A counted horizontal rectangle--pentagon term forces the X-marking in the turn row
to lie in the first commuted column. -/
theorem X_column_eq_turnRow_of_mem_rectanglePentagonOppositeSideOrder (x : GridState n)
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectanglePentagonOppositeSideOrder C x) : G.X C.column = C.turnRow := by
  obtain ⟨hcount, hleft, -⟩ := (G.mem_rectanglePentagonOppositeSideOrder C x D).1 hD
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcount
  exact (D.disjoint_XSet_iff_X_column_eq_turnRow_of_opposite_side_order G hleft
    (G.rectangle_top_eq_finRotate_bottom_of_mem_rectanglePentagonOppositeSideOrder C x D hD)).1
      ⟨((G.mem_unblockedRectangles _).1 hr).2, ((G.mem_pentagons _).1 hP).2⟩

/-- A counted horizontal pentagon--rectangle term forces the X-marking in the turn row
to lie in the second commuted column. -/
theorem X_next_eq_turnRow_of_mem_pentagonRectangleOppositeSideOrder (x : GridState n)
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.pentagonRectangleOppositeSideOrder C x) :
    G.X (finRotate n C.column) = C.turnRow := by
  obtain ⟨hcount, hleft, -⟩ := (G.mem_pentagonRectangleOppositeSideOrder C x D).1 hD
  obtain ⟨hP, hr⟩ := (G.mem_pentagonRectangleDecompositions C D).1 hcount
  exact (D.disjoint_XSet_swapColumns_iff_X_next_eq_turnRow_of_opposite_side_order G hleft
    (G.pentagon_top_eq_finRotate_bottom_of_mem_pentagonRectangleOppositeSideOrder C x D hD)).1
      ⟨((G.mem_pentagons _).1 hP).2,
        (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hr).2⟩

/-- The horizontal rectangle--pentagon family is empty unless the first commuted column's
X-marking lies in the turn row. -/
@[simp]
theorem rectanglePentagonOppositeSideOrder_eq_empty_of_X_column_ne_turnRow (x : GridState n)
    (hX : G.X C.column ≠ C.turnRow) : G.rectanglePentagonOppositeSideOrder C x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro D hD
  exact hX (G.X_column_eq_turnRow_of_mem_rectanglePentagonOppositeSideOrder C x D hD)

/-- The horizontal pentagon--rectangle family is empty unless the second commuted column's
X-marking lies in the turn row. -/
@[simp]
theorem pentagonRectangleOppositeSideOrder_eq_empty_of_X_next_ne_turnRow (x : GridState n)
    (hX : haveI := C.column.neZero; G.X (C.column + 1) ≠ C.turnRow) :
    G.pentagonRectangleOppositeSideOrder C x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro D hD
  exact hX (by simpa only [finRotate_apply] using
    G.X_next_eq_turnRow_of_mem_pentagonRectangleOppositeSideOrder C x D hD)

/-- At least one horizontal family in the diagonal pentagon chain-map equation is empty.
The two commuted columns cannot have their X-markings in the same turn row. -/
theorem rectanglePentagonOppositeSideOrder_eq_empty_or_pentagonRectangleOppositeSideOrder_eq_empty
    (x : GridState n) :
    G.rectanglePentagonOppositeSideOrder C x = ∅ ∨
      G.pentagonRectangleOppositeSideOrder C x = ∅ := by
  by_cases hX : G.X C.column = C.turnRow
  · right
    apply G.pentagonRectangleOppositeSideOrder_eq_empty_of_X_next_ne_turnRow C x
    intro hX'
    exact C.column_ne_next (by simpa only [finRotate_apply] using
      (G.X.toPerm.injective (hX.trans hX'.symm)))
  · exact Or.inl (G.rectanglePentagonOppositeSideOrder_eq_empty_of_X_column_ne_turnRow C x hX)

end GridDiagram

end TauCeti
