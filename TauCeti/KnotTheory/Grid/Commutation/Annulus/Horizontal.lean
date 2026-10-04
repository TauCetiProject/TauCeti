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

/-- A pentagon spanning one cyclic row has its turn in that row and covers only the
columns of its underlying rectangle other than the first commuted column. -/
theorem coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom
    (P : GridPentagonBetween a s x y) (hthin : P.top = finRotate n P.bottom) :
    P.coveredSquares = (Grid.cIco P.left (finRotate n a)).erase a ×ˢ {s} := by
  have hrows : Grid.cIco P.bottom P.top = {P.bottom} :=
    Grid.cIco_eq_singleton_iff.2 ⟨rfl, hthin, P.bottom_ne_top⟩
  have hs : s = P.bottom := by
    have ht : s ∈ Grid.cIco P.bottom P.top := P.turn_mem
    rw [hrows] at ht
    exact Finset.mem_singleton.mp ht
  ext p
  simp only [mem_coveredSquares, Finset.mem_product, Finset.mem_erase,
    hs, hrows, Finset.mem_singleton]
  simp only [hthin, Grid.cIoo_finRotate_eq_empty, Grid.cIco_self,
    Finset.notMem_empty, and_false, or_false, and_assoc]

end GridPentagonBetween

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- A thin horizontal rectangle--pentagon annulus covers the turn row except for the
first commuted column. This is a statement about markings, not interior grid points. -/
theorem coveredSquares_union_of_opposite_side_order
    (D : GridRectanglePentagonDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hright : D.rectangle.right = D.pentagon.left)
    (hthin : D.rectangle.top = finRotate n D.rectangle.bottom) :
    D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.coveredSquares =
      (Finset.univ.erase a) ×ˢ {s} := by
  have hbottom : D.pentagon.bottom = D.rectangle.bottom := by
    rw [GridRectangleBetween.bottom_def, ← hright, D.rectangle.map_right,
      GridRectangleBetween.bottom_def]
  have htop : D.pentagon.top = D.rectangle.top := by
    rw [GridRectangleBetween.top_def, ← hleft, D.rectangle.map_left,
      GridRectangleBetween.top_def]
  have hrows : Grid.cIco D.rectangle.bottom D.rectangle.top = {s} := by
    have h := Grid.cIco_eq_singleton_iff.2
      ⟨rfl, hthin, D.rectangle.bottom_ne_top⟩
    have hs : s = D.rectangle.bottom := by
      have ht : s ∈ Grid.cIco D.pentagon.bottom D.pentagon.top := D.pentagon.turn_mem
      rw [hbottom, htop, h] at ht
      exact Finset.mem_singleton.mp ht
    simpa only [hs] using h
  rw [D.pentagon.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom
    (htop.trans (hthin.trans (congrArg (finRotate n) hbottom).symm))]
  have hcols := Grid.cIco_union_swap D.pentagon.left_ne
  have hnot : a ∉ Grid.cIco (finRotate n a) D.pentagon.left := by simp
  ext p
  simp only [Finset.mem_union, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    hleft, hright, D.pentagon.right_eq, hrows, Finset.mem_product,
    Finset.mem_erase, Finset.mem_univ, Finset.mem_singleton, and_true]
  have hp : p.1 ∈ Grid.cIco D.pentagon.left (finRotate n a) ∨
      p.1 ∈ Grid.cIco (finRotate n a) D.pentagon.left := by
    rw [← Finset.mem_union, hcols]
    exact Finset.mem_univ _
  grind

/-- The two domains of a thin horizontal rectangle--pentagon annulus avoid X-markings
exactly when the first commuted column contains the X-marking in the turn row. -/
theorem disjoint_XSet_iff_of_opposite_side_order
    (D : GridRectanglePentagonDecomposition a s x x) (G : GridDiagram n)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hright : D.rectangle.right = D.pentagon.left)
    (hthin : D.rectangle.top = finRotate n D.rectangle.bottom) :
    Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet ∧
        Disjoint D.pentagon.coveredSquares G.XSet ↔ G.X a = s := by
  rw [← Finset.disjoint_union_left,
    D.coveredSquares_union_of_opposite_side_order hleft hright hthin]
  exact G.X.disjoint_univ_erase_product_singleton_pointSet_iff a s

end GridRectanglePentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- Reading the rectangle of a thin horizontal pentagon--rectangle annulus back in the
original columns gives the turn row except for the second commuted column. -/
theorem coveredSquares_union_map_of_opposite_side_order
    (D : GridPentagonRectangleDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hright : D.rectangle.right = D.pentagon.left)
    (hthin : D.pentagon.top = finRotate n D.pentagon.bottom) :
    D.pentagon.coveredSquares ∪ D.rectangle.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      (Finset.univ.erase (finRotate n a)) ×ˢ {s} := by
  classical
  have hbottom : D.rectangle.bottom = D.pentagon.bottom := by
    simp only [GridRectangleBetween.bottom_def, hleft, D.pentagon.map_right]
  have htop : D.rectangle.top = D.pentagon.top := by
    simp only [GridRectangleBetween.top_def, hright, D.pentagon.map_left]
  have hrows : Grid.cIco D.pentagon.bottom D.pentagon.top = {s} := by
    have h := Grid.cIco_eq_singleton_iff.2 ⟨rfl, hthin, D.pentagon.bottom_ne_top⟩
    have hs : s = D.pentagon.bottom := by
      have ht : s ∈ Grid.cIco D.pentagon.bottom D.pentagon.top := D.pentagon.turn_mem
      rw [h] at ht
      exact Finset.mem_singleton.mp ht
    simpa only [hs] using h
  rw [D.pentagon.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom hthin]
  -- Away from the two commuted columns, the complementary column arcs still partition the row.
  have hcols := Grid.cIco_union_swap D.pentagon.left_ne
  have ha : a ∈ Grid.cIco D.pentagon.left (finRotate n a) :=
    Grid.self_mem_cIco_finRotate D.pentagon.left_ne
  have hnot : a ∉ Grid.cIco (finRotate n a) D.pentagon.left := by simp
  have hb : finRotate n a ∈ Grid.cIco (finRotate n a) D.pentagon.left :=
    Grid.left_mem_cIco D.pentagon.left_ne.symm
  ext p
  have hmap : p ∈ D.rectangle.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
      (Equiv.swap a (finRotate n a) p.1, p.2) ∈ D.rectangle.toGridRectangle.coveredSquares := by
    simp
  simp only [Finset.mem_union, hmap, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    hleft, hright, D.pentagon.right_eq, hbottom, htop, hrows, Finset.mem_product,
    Finset.mem_erase, Finset.mem_univ, Finset.mem_singleton, and_true]
  have hp : p.1 ∈ Grid.cIco D.pentagon.left (finRotate n a) ∨
      p.1 ∈ Grid.cIco (finRotate n a) D.pentagon.left := by
    rw [← Finset.mem_union, hcols]
    exact Finset.mem_univ _
  have hab : a ≠ finRotate n a := by
    intro h
    exact Grid.right_notMem_cIco D.pentagon.left (finRotate n a) (h ▸ ha)
  have hbnot := Grid.right_notMem_cIco D.pentagon.left (finRotate n a)
  -- The rectangle's column swap moves the missing square from the first column to the second.
  by_cases hpa : p.1 = a
  · simp only [hpa, Equiv.swap_apply_left, hb, hab, not_false_eq_true,
      true_and, ne_eq, not_true_eq_false, false_and, false_or]
  · by_cases hpb : p.1 = finRotate n a
    · simp only [hpb, Equiv.swap_apply_right, hbnot, hnot, ne_eq, not_true_eq_false,
        false_and, and_false, or_false]
    · rw [Equiv.swap_apply_of_ne_of_ne hpa hpb]
      grind

/-- For a thin horizontal pentagon--rectangle annulus, with the rectangle tested against
the commuted diagram, X-avoidance is equivalent to the second commuted column containing
the X-marking in the turn row. -/
theorem disjoint_XSet_iff_of_opposite_side_order
    (D : GridPentagonRectangleDecomposition a s x x) (G : GridDiagram n)
    (hleft : D.rectangle.left = D.pentagon.right)
    (hright : D.rectangle.right = D.pentagon.left)
    (hthin : D.pentagon.top = finRotate n D.pentagon.bottom) :
    Disjoint D.pentagon.coveredSquares G.XSet ∧
        Disjoint D.rectangle.toGridRectangle.coveredSquares
          (G.swapColumns a (finRotate n a)).XSet ↔ G.X (finRotate n a) = s := by
  classical
  let e := ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding
  have hX : G.XSet = (G.swapColumns a (finRotate n a)).XSet.map e := by
    ext p
    simp [e, G.mem_XSet_swapColumns]
  have hdisjoint : Disjoint (D.rectangle.toGridRectangle.coveredSquares.map e) G.XSet ↔
      Disjoint D.rectangle.toGridRectangle.coveredSquares
        (G.swapColumns a (finRotate n a)).XSet := by
    rw [hX, Finset.disjoint_map]
  rw [← hdisjoint, ← Finset.disjoint_union_left,
    D.coveredSquares_union_map_of_opposite_side_order hleft hright hthin]
  exact G.X.disjoint_univ_erase_product_singleton_pointSet_iff (finRotate n a) s

end GridPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- A counted horizontal rectangle--pentagon term forces the X-marking in the turn row
to lie in the first commuted column. -/
theorem X_eq_turnRow_of_mem_rectanglePentagonOppositeSideOrder (x : GridState n)
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectanglePentagonOppositeSideOrder C x) : G.X C.column = C.turnRow := by
  obtain ⟨hcount, hleft, hright⟩ := (G.mem_rectanglePentagonOppositeSideOrder C x D).1 hD
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcount
  exact (D.disjoint_XSet_iff_of_opposite_side_order G hleft hright
    (G.rectangle_top_eq_finRotate_bottom_of_mem_rectanglePentagonOppositeSideOrder C x D hD)).1
      ⟨((G.mem_unblockedRectangles _).1 hr).2, ((G.mem_pentagons _).1 hP).2⟩

/-- A counted horizontal pentagon--rectangle term forces the X-marking in the turn row
to lie in the second commuted column. -/
theorem X_eq_turnRow_of_mem_pentagonRectangleOppositeSideOrder (x : GridState n)
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.pentagonRectangleOppositeSideOrder C x) :
    G.X (finRotate n C.column) = C.turnRow := by
  obtain ⟨hcount, hleft, hright⟩ := (G.mem_pentagonRectangleOppositeSideOrder C x D).1 hD
  obtain ⟨hP, hr⟩ := (G.mem_pentagonRectangleDecompositions C D).1 hcount
  exact (D.disjoint_XSet_iff_of_opposite_side_order G hleft hright
    (G.pentagon_top_eq_finRotate_bottom_of_mem_pentagonRectangleOppositeSideOrder C x D hD)).1
      ⟨((G.mem_pentagons _).1 hP).2,
        (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hr).2⟩

/-- The horizontal rectangle--pentagon family is empty unless the first commuted column's
X-marking lies in the turn row. -/
@[simp]
theorem rectanglePentagonOppositeSideOrder_eq_empty (x : GridState n)
    (hX : G.X C.column ≠ C.turnRow) : G.rectanglePentagonOppositeSideOrder C x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro D hD
  exact hX (G.X_eq_turnRow_of_mem_rectanglePentagonOppositeSideOrder C x D hD)

/-- The horizontal pentagon--rectangle family is empty unless the second commuted column's
X-marking lies in the turn row. -/
theorem pentagonRectangleOppositeSideOrder_eq_empty (x : GridState n)
    (hX : G.X (finRotate n C.column) ≠ C.turnRow) :
    G.pentagonRectangleOppositeSideOrder C x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro D hD
  exact hX (G.X_eq_turnRow_of_mem_pentagonRectangleOppositeSideOrder C x D hD)

/-- At least one horizontal family in the diagonal pentagon chain-map equation is empty.
The two commuted columns cannot have their X-markings in the same turn row. -/
theorem rectanglePentagonOppositeSideOrder_eq_empty_or_pentagonRectangleOppositeSideOrder_eq_empty
    (x : GridState n) :
    G.rectanglePentagonOppositeSideOrder C x = ∅ ∨
      G.pentagonRectangleOppositeSideOrder C x = ∅ := by
  by_cases hX : G.X C.column = C.turnRow
  · right
    apply G.pentagonRectangleOppositeSideOrder_eq_empty C x
    intro hX'
    exact C.column_ne_next (G.X.toPerm.injective (hX.trans hX'.symm))
  · exact Or.inl (G.rectanglePentagonOppositeSideOrder_eq_empty C x hX)

end GridDiagram

end TauCeti
