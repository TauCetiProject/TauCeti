/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Empty

/-!
# X-markings in horizontal initial-side commutation annuli

A thin horizontal rectangle followed by an initial-side pentagon covers the turn row with the
second commuted column missing. In the opposite composition order, reading the rectangle back in
the original diagram moves the missing square to the first commuted column. Thus the two domains
avoid all X-markings exactly when the X-marking in the turn row occupies the missing square.

These marking tests characterize which horizontal initial-side terms can occur in the diagonal
coefficient of the commutation chain-map equation. The two composition orders cannot both occur,
because distinct columns of a grid diagram have X-markings in distinct rows.

## References

Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6.
-/

public section

namespace TauCeti

namespace GridInitialPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- Swapping the two commuted columns preserves the covered squares of a thin initial-side
pentagon, since it covers neither commuted column. -/
private theorem coveredSquares_map_swap_eq_of_top_eq_finRotate_bottom
    (P : GridInitialPentagonBetween a s x y) (hthin : P.top = finRotate n P.bottom) :
    P.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      P.coveredSquares := by
  classical
  rw [P.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom hthin]
  ext p
  simp only [Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    Finset.mem_product, Finset.mem_erase, Finset.mem_singleton]
  have hanot : a ∉ Grid.cIco (finRotate n a) P.right := by simp
  by_cases ha : p.1 = a
  · simp only [ha, Equiv.swap_apply_left, hanot, and_false, false_and,
      ne_eq, not_true_eq_false]
  · by_cases hb : p.1 = finRotate n a
    · simp only [hb, Equiv.swap_apply_right, hanot, and_false, false_and,
        ne_eq, not_true_eq_false]
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A thin initial-side pentagon and a rectangle on the complementary column arc cover the turn
row except for the second commuted column. -/
theorem coveredSquares_union_of_opposite_side_order (P : GridInitialPentagonBetween a s x y)
    (r : GridRectangle n) (hthin : P.top = finRotate n P.bottom)
    (hleft : r.left = P.right) (hright : r.right = finRotate n a)
    (hbottom : r.bottom = P.bottom) (htop : r.top = P.top) :
    P.coveredSquares ∪ r.coveredSquares =
      (Finset.univ.erase (finRotate n a)) ×ˢ {s} := by
  rw [P.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom hthin]
  have hrows := P.cIco_bottom_top_eq_singleton_of_top_eq_finRotate_bottom hthin
  have hcols := Grid.cIco_union_swap P.right_ne.symm
  have hnot := Grid.right_notMem_cIco P.right (finRotate n a)
  ext p
  simp only [Finset.mem_union, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    hleft, hright, hbottom, htop, hrows, Finset.mem_product,
    Finset.mem_erase, Finset.mem_univ, Finset.mem_singleton, and_true]
  have hp : p.1 ∈ Grid.cIco (finRotate n a) P.right ∨
      p.1 ∈ Grid.cIco P.right (finRotate n a) := by
    rw [← Finset.mem_union, hcols]
    exact Finset.mem_univ _
  grind

/-- A thin initial-side pentagon and a rectangle on its complementary column arc cover disjoint
squares. -/
theorem disjoint_coveredSquares_of_opposite_side_order
    (P : GridInitialPentagonBetween a s x y) (r : GridRectangle n)
    (hthin : P.top = finRotate n P.bottom)
    (hleft : r.left = P.right) (hright : r.right = finRotate n a) :
    Disjoint P.coveredSquares r.coveredSquares := by
  rw [P.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom hthin,
    GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def, hleft, hright]
  exact Finset.disjoint_product.2 (Or.inl
    ((Grid.disjoint_cIco_swap (finRotate n a) P.right).mono_left (Finset.erase_subset _ _)))

end GridInitialPentagonBetween

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- A thin horizontal rectangle--initial-side pentagon annulus covers the turn row except for
the second commuted column. -/
theorem coveredSquares_union_of_opposite_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.right)
    (hthin : D.first.top = finRotate n D.first.bottom) :
    D.first.toGridRectangle.coveredSquares ∪ D.pentagon.coveredSquares =
      (Finset.univ.erase (finRotate n a)) ×ˢ {s} := by
  have hleft' : D.first.left = D.pentagon.right := by
    simpa only [pentagon_toGridRectangleBetween] using hleft
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.first hleft'
  have hbottom := D.first.bottom_eq_bottom_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  have htop := D.first.top_eq_top_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  rw [Finset.union_comm]
  exact D.pentagon.coveredSquares_union_of_opposite_side_order D.first.toGridRectangle
    (htop.trans (hthin.trans (congrArg (finRotate n) hbottom).symm)) hleft'
    (hright.trans D.pentagon.left_eq) hbottom.symm htop.symm

/-- The constituent domains of a thin horizontal rectangle--initial-side pentagon annulus cover
disjoint squares. -/
theorem disjoint_coveredSquares_of_opposite_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.right)
    (hthin : D.first.top = finRotate n D.first.bottom) :
    Disjoint D.first.toGridRectangle.coveredSquares D.pentagon.coveredSquares := by
  have hleft' : D.first.left = D.pentagon.right := by
    simpa only [pentagon_toGridRectangleBetween] using hleft
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.first hleft'
  have hbottom := D.first.bottom_eq_bottom_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  have htop := D.first.top_eq_top_of_left_eq_right
    D.pentagon.toGridRectangleBetween hright.symm
  have hPthin := htop.trans (hthin.trans (congrArg (finRotate n) hbottom).symm)
  exact (D.pentagon.disjoint_coveredSquares_of_opposite_side_order D.first.toGridRectangle
    hPthin hleft' (hright.trans D.pentagon.left_eq)).symm

/-- The two domains of a thin horizontal rectangle--initial-side pentagon annulus avoid
X-markings exactly when the second commuted column contains the X-marking in the turn row. -/
theorem disjoint_XSet_iff_X_next_eq_turnRow_of_opposite_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x) (G : GridDiagram n)
    (hleft : D.first.left = D.second.right)
    (hthin : D.first.top = finRotate n D.first.bottom) :
    Disjoint D.first.toGridRectangle.coveredSquares G.XSet ∧
        Disjoint D.pentagon.coveredSquares G.XSet ↔ G.X (finRotate n a) = s := by
  rw [← Finset.disjoint_union_left,
    D.coveredSquares_union_of_opposite_side_order hleft hthin]
  exact G.X.disjoint_univ_erase_product_singleton_pointSet_iff (finRotate n a) s

end GridRectangleInitialPentagonDecomposition

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- Reading the rectangle of a thin horizontal initial-side pentagon--rectangle annulus back in
the original columns gives the turn row except for the first commuted column. -/
theorem coveredSquares_union_map_of_opposite_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x)
    (hleft : D.second.left = D.first.right)
    (hthin : D.first.top = finRotate n D.first.bottom) :
    D.pentagon.coveredSquares ∪ D.second.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      (Finset.univ.erase a) ×ˢ {s} := by
  classical
  have hleft' : D.second.left = D.pentagon.right := by
    simpa only [pentagon_toGridRectangleBetween] using hleft
  have hthin' : D.pentagon.top = finRotate n D.pentagon.bottom := by
    simpa only [pentagon_toGridRectangleBetween] using hthin
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.second hleft'
  have hbottom := D.pentagon.toGridRectangleBetween.bottom_eq_bottom_of_left_eq_right
    D.second hleft'
  have htop := D.pentagon.toGridRectangleBetween.top_eq_top_of_left_eq_right
    D.second hleft'
  let e := ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding
  have hunion := congrArg (fun S : Finset (Fin n × Fin n) => S.map e)
    (D.pentagon.coveredSquares_union_of_opposite_side_order D.second.toGridRectangle
      hthin' hleft' (hright.trans D.pentagon.left_eq) hbottom htop)
  rw [Finset.map_union,
    D.pentagon.coveredSquares_map_swap_eq_of_top_eq_finRotate_bottom hthin'] at hunion
  rw [hunion]
  ext p
  simp only [e, Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    Finset.mem_product, Finset.mem_erase, Finset.mem_univ, Finset.mem_singleton, and_true,
    ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

/-- The initial-side pentagon and the rectangle read back in the original columns cover disjoint
squares in a thin horizontal annulus. -/
theorem disjoint_coveredSquares_map_of_opposite_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x)
    (hleft : D.second.left = D.first.right)
    (hthin : D.first.top = finRotate n D.first.bottom) :
    Disjoint D.pentagon.coveredSquares (D.second.toGridRectangle.coveredSquares.map
      ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding) := by
  have hleft' : D.second.left = D.pentagon.right := by
    simpa only [pentagon_toGridRectangleBetween] using hleft
  have hthin' : D.pentagon.top = finRotate n D.pentagon.bottom := by
    simpa only [pentagon_toGridRectangleBetween] using hthin
  have hright := D.pentagon.toGridRectangleBetween.right_eq_left_of_left_eq_right
    D.second hleft'
  let e := ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding
  have hdisjoint := D.pentagon.disjoint_coveredSquares_of_opposite_side_order
    D.second.toGridRectangle hthin' hleft' (hright.trans D.pentagon.left_eq)
  have h := (Finset.disjoint_map e).2 hdisjoint
  rwa [D.pentagon.coveredSquares_map_swap_eq_of_top_eq_finRotate_bottom hthin'] at h

/-- For a thin horizontal initial-side pentagon--rectangle annulus, with the rectangle tested
against the commuted diagram, X-avoidance is equivalent to the first commuted column containing
the X-marking in the turn row. -/
theorem disjoint_XSet_swapColumns_iff_X_column_eq_turnRow_of_opposite_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x) (G : GridDiagram n)
    (hleft : D.second.left = D.first.right)
    (hthin : D.first.top = finRotate n D.first.bottom) :
    Disjoint D.pentagon.coveredSquares G.XSet ∧
        Disjoint D.second.toGridRectangle.coveredSquares
          (G.swapColumns a (finRotate n a)).XSet ↔ G.X a = s := by
  rw [← G.disjoint_map_swapColumns_XSet_iff a (finRotate n a),
    ← Finset.disjoint_union_left,
    D.coveredSquares_union_map_of_opposite_side_order hleft hthin]
  exact G.X.disjoint_univ_erase_product_singleton_pointSet_iff a s

end GridInitialPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- A counted horizontal rectangle--initial-side pentagon term forces the X-marking in the turn
row to lie in the second commuted column. -/
theorem X_next_eq_turnRow_of_mem_rectangleInitialPentagonOppositeSideOrder (x : GridState n)
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectangleInitialPentagonOppositeSideOrder C x) :
    G.X (finRotate n C.column) = C.turnRow := by
  obtain ⟨hcount, hleft, -⟩ := (G.mem_rectangleInitialPentagonOppositeSideOrder C x D).1 hD
  obtain ⟨hr, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcount
  exact (D.disjoint_XSet_iff_X_next_eq_turnRow_of_opposite_side_order G hleft
    (G.rectangle_top_eq_finRotate_bottom_of_mem_rectangleInitialPentagonOppositeSideOrder
      C x D hD)).1
      ⟨((G.mem_unblockedRectangles _).1 hr).2, ((G.mem_initialPentagons _).1 hP).2⟩

/-- A counted horizontal initial-side pentagon--rectangle term forces the X-marking in the turn
row to lie in the first commuted column. -/
theorem X_column_eq_turnRow_of_mem_initialPentagonRectangleOppositeSideOrder (x : GridState n)
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.initialPentagonRectangleOppositeSideOrder C x) :
    G.X C.column = C.turnRow := by
  obtain ⟨hcount, hleft, -⟩ := (G.mem_initialPentagonRectangleOppositeSideOrder C x D).1 hD
  obtain ⟨hP, hr⟩ := (G.mem_initialPentagonRectangleDecompositions C D).1 hcount
  exact (D.disjoint_XSet_swapColumns_iff_X_column_eq_turnRow_of_opposite_side_order G hleft
    (G.pentagon_top_eq_finRotate_bottom_of_mem_initialPentagonRectangleOppositeSideOrder
      C x D hD)).1
      ⟨((G.mem_initialPentagons _).1 hP).2,
        (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hr).2⟩

/-- The horizontal rectangle--initial-side pentagon family is empty unless the second commuted
column's X-marking lies in the turn row. -/
@[simp]
theorem rectangleInitialPentagonOppositeSideOrder_eq_empty_of_X_next_ne_turnRow
    (x : GridState n)
    (hX : haveI := C.column.neZero; G.X (C.column + 1) ≠ C.turnRow) :
    G.rectangleInitialPentagonOppositeSideOrder C x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro D hD
  exact hX (by simpa only [finRotate_apply] using
    G.X_next_eq_turnRow_of_mem_rectangleInitialPentagonOppositeSideOrder C x D hD)

/-- The horizontal initial-side pentagon--rectangle family is empty unless the first commuted
column's X-marking lies in the turn row. -/
@[simp]
theorem initialPentagonRectangleOppositeSideOrder_eq_empty_of_X_column_ne_turnRow
    (x : GridState n) (hX : G.X C.column ≠ C.turnRow) :
    G.initialPentagonRectangleOppositeSideOrder C x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro D hD
  exact hX (G.X_column_eq_turnRow_of_mem_initialPentagonRectangleOppositeSideOrder C x D hD)

/-- At least one horizontal initial-side family in the diagonal commutation chain-map equation is
empty. The two commuted columns cannot have their X-markings in the same turn row. -/
theorem one_horizontalInitialPentagonFamily_eq_empty
    (x : GridState n) :
    G.rectangleInitialPentagonOppositeSideOrder C x = ∅ ∨
      G.initialPentagonRectangleOppositeSideOrder C x = ∅ := by
  by_cases hX : G.X C.column = C.turnRow
  · left
    apply G.rectangleInitialPentagonOppositeSideOrder_eq_empty_of_X_next_ne_turnRow C x
    intro hX'
    exact C.column_ne_next (by simpa only [finRotate_apply] using
      (G.X.toPerm.injective (hX.trans hX'.symm)))
  · exact Or.inr
      (G.initialPentagonRectangleOppositeSideOrder_eq_empty_of_X_column_ne_turnRow C x hX)

end GridDiagram

end TauCeti
