/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon
public import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty

/-!
# Vertical annuli with initial-side pentagons

A returning rectangle and an initial-side pentagon with the same ordered side columns
form a vertical annulus. Simultaneous emptiness forces its width to be one column, starting
at the replaced line. The pentagon's marking domain then occupies only the two commuted
columns. The rectangle is read in the original diagram when it precedes the pentagon, and
in the commuted diagram when it follows it.

This file gives the covered-square unions and exact marking tests in both orders. The
characterizations of counted pairs discharge emptiness rather than assuming it. They supply
the initial-side vertical terms of the diagonal commutation chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6. The square-union arguments follow the terminal-side annulus
calculations in `TauCeti.KnotTheory.Grid.Commutation.Annulus.Vertical`.
-/

public section

namespace TauCeti

namespace GridInitialPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- In a thin initial-side pentagon, the marking domain consists of the upper open arc in
the first commuted column and the lower half-open arc in the second. -/
theorem coveredSquares_of_right_eq_finRotate (P : GridInitialPentagonBetween a s x y)
    (hthin : P.right = finRotate n (finRotate n a)) :
    P.coveredSquares =
      ({a} ×ˢ Grid.cIoo s P.top) ∪ ({finRotate n a} ×ˢ Grid.cIco P.bottom s) := by
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    simpa only [P.left_eq, hthin] using P.left_ne_right
  have hcols := Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩
  ext p
  simp only [P.mem_coveredSquares, hthin, hcols, Finset.mem_union,
    Finset.mem_product, Finset.mem_singleton]
  tauto

/-- A rectangle followed by an initial-side pentagon, returning to its source with the
same side order, covers an upper open arc in the first commuted column and its complementary
half-open arc in the second. -/
theorem coveredSquares_union_rectangle_of_same_side_order
    (P : GridInitialPentagonBetween a s y x) (r : GridRectangleBetween x y)
    (hleft : r.left = P.left) (hthin : P.right = finRotate n (finRotate n a)) :
    r.toGridRectangle.coveredSquares ∪ P.coveredSquares =
      ({a} ×ˢ Grid.cIoo s P.top) ∪ ({finRotate n a} ×ˢ Grid.cIco P.top s) := by
  have hright := P.toGridRectangleBetween.right_eq_right_of_left_eq_left r hleft
  have hbottom := P.toGridRectangleBetween.bottom_eq_top_of_left_eq_left r hleft
  have htop := P.toGridRectangleBetween.top_eq_bottom_of_left_eq_left r hleft
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    simpa only [P.left_eq, hthin] using P.left_ne_right
  have hcols := Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩
  have hrows : Grid.cIco P.top P.bottom ∪ Grid.cIco P.bottom s = Grid.cIco P.top s := by
    by_cases hs : s = P.bottom
    · simp [hs]
    · exact Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo
        (Grid.mem_cIoo_cyclic_right
          (Grid.mem_cIoo_of_mem_cIco P.turn_mem_cIco_bottom_top hs))
  rw [P.coveredSquares_of_right_eq_finRotate hthin]
  ext p
  simp only [Finset.mem_union, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    hleft, hright, hbottom, htop, P.left_eq, hthin, hcols,
    Finset.mem_product, Finset.mem_singleton]
  have := Finset.ext_iff.mp hrows p.2
  simp only [Finset.mem_union] at this
  grind

/-- Avoiding a marking state in a thin rectangle--initial-pentagon annulus is exactly
avoiding the two covered arcs in the commuted columns. -/
theorem disjoint_pointSet_iff_of_rectangle_same_side_order
    (P : GridInitialPentagonBetween a s y x) (r : GridRectangleBetween x y)
    (M : GridState n) (hleft : r.left = P.left)
    (hthin : P.right = finRotate n (finRotate n a)) :
    Disjoint r.toGridRectangle.coveredSquares M.pointSet ∧
        Disjoint P.coveredSquares M.pointSet ↔
      M a ∉ Grid.cIoo s P.top ∧ M (finRotate n a) ∉ Grid.cIco P.top s := by
  rw [← Finset.disjoint_union_left,
    P.coveredSquares_union_rectangle_of_same_side_order r hleft hthin,
    Finset.disjoint_union_left, M.disjoint_product_pointSet_iff,
    M.disjoint_product_pointSet_iff]
  simp

/-- An initial-side pentagon followed by a returning rectangle covers the complementary
closed-arc omission in the first commuted column and the lower half-open arc in the second.
The rectangle's squares are transported back from the commuted diagram. -/
theorem coveredSquares_union_map_rectangle_of_same_side_order
    (P : GridInitialPentagonBetween a s x y) (r : GridRectangleBetween y x)
    (hleft : r.left = P.left) (hthin : P.right = finRotate n (finRotate n a)) :
    P.coveredSquares ∪ r.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      ({a} ×ˢ (Finset.univ \ insert s (Grid.cIco P.bottom s))) ∪
        ({finRotate n a} ×ˢ Grid.cIco P.bottom s) := by
  classical
  have hright := P.toGridRectangleBetween.right_eq_right_of_left_eq_left r hleft
  have hbottom := P.toGridRectangleBetween.bottom_eq_top_of_left_eq_left r hleft
  have htop := P.toGridRectangleBetween.top_eq_bottom_of_left_eq_left r hleft
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    simpa only [P.left_eq, hthin] using P.left_ne_right
  have hcols := Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩
  have hrows (t : Fin n) :
      (t ∈ Grid.cIco P.top P.bottom ∨ t ∈ Grid.cIoo s P.top) ↔
        t ∉ insert s (Grid.cIco P.bottom s) := by
    have hsplit := Grid.ite_mem_cIco_eq_add_add P.turn_mem_cIco_bottom_top t
    have hcover : t ∈ Grid.cIco P.bottom P.top ∨ t ∈ Grid.cIco P.top P.bottom := by
      rw [← Finset.mem_union, Grid.cIco_union_swap P.bottom_ne_top]
      exact Finset.mem_univ t
    have hdisjoint := Finset.disjoint_left.mp (Grid.disjoint_cIco_swap P.bottom P.top)
    simp only [Finset.mem_insert]
    split_ifs at hsplit <;> grind
  rw [P.coveredSquares_of_right_eq_finRotate hthin]
  ext p
  simp only [Finset.mem_union, Finset.mem_map_equiv, Equiv.prodCongr_symm,
    Equiv.symm_swap, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply',
    Equiv.refl_apply, GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, hleft, hright, hbottom, htop, P.left_eq,
    hthin, hcols, Finset.mem_product, Finset.mem_singleton, Equiv.swap_apply_eq_iff,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  have := hrows p.2
  grind

/-- The marking test for a thin initial-pentagon--rectangle annulus, with the rectangle
read in the commuted marking state. -/
theorem disjoint_pointSet_swapColumns_iff_of_rectangle_same_side_order
    (P : GridInitialPentagonBetween a s x y) (r : GridRectangleBetween y x)
    (M : GridState n) (hleft : r.left = P.left)
    (hthin : P.right = finRotate n (finRotate n a)) :
    Disjoint P.coveredSquares M.pointSet ∧
        Disjoint r.toGridRectangle.coveredSquares (M.swapColumns a (finRotate n a)).pointSet ↔
      M a ∈ insert s (Grid.cIco P.bottom s) ∧
        M (finRotate n a) ∉ Grid.cIco P.bottom s := by
  rw [GridState.swapColumns,
    ← M.disjoint_map_relabelColumns_pointSet_iff (Equiv.swap a (finRotate n a)),
    Equiv.symm_swap, ← Finset.disjoint_union_left,
    P.coveredSquares_union_map_rectangle_of_same_side_order r hleft hthin,
    Finset.disjoint_union_left, M.disjoint_product_pointSet_iff,
    M.disjoint_product_pointSet_iff]
  simp only [Finset.mem_singleton, forall_eq, Finset.mem_sdiff, Finset.mem_univ,
    true_and, not_not]

end GridInitialPentagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x y : GridState n}

/-- A same-side-order returning rectangle--initial-pentagon pair is counted exactly when
it is thin and its two covered arcs avoid the X-markings. -/
theorem mem_unblockedRectangles_and_mem_initialPentagons_iff_of_same_side_order
    (r : GridRectangleBetween x y) (P : GridInitialPentagonBetween C.column C.turnRow y x)
    (hleft : r.left = P.left) :
    r ∈ G.unblockedRectangles x y ∧ P ∈ G.initialPentagons C y x ↔
      P.right = finRotate n (finRotate n C.column) ∧
        G.X C.column ∉ Grid.cIoo C.turnRow P.top ∧
          G.X (finRotate n C.column) ∉ Grid.cIco P.top C.turnRow := by
  constructor
  · rintro ⟨hr, hP⟩
    obtain ⟨her, har⟩ := (G.mem_unblockedRectangles r).1 hr
    obtain ⟨heP, haP⟩ := (G.mem_initialPentagons P).1 hP
    have hthin :=
      (P.toGridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
        r hleft).1 ⟨heP, her⟩
    rw [P.left_eq] at hthin
    exact ⟨hthin, (P.disjoint_pointSet_iff_of_rectangle_same_side_order r G.X hleft hthin).1
      ⟨har, haP⟩⟩
  · rintro ⟨hthin, hX⟩
    have hempty :=
      (P.toGridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
        r hleft).2 (by simpa only [P.left_eq] using hthin)
    have havoid := (P.disjoint_pointSet_iff_of_rectangle_same_side_order r G.X hleft hthin).2 hX
    exact ⟨(G.mem_unblockedRectangles r).2 ⟨hempty.2, havoid.1⟩,
      (G.mem_initialPentagons P).2 ⟨hempty.1, havoid.2⟩⟩

/-- A same-side-order returning initial-pentagon--rectangle pair is counted exactly when
it is thin and its marking test holds, reading the rectangle in the commuted diagram. -/
theorem mem_initialPentagons_and_mem_unblockedRectangles_iff_of_same_side_order
    (P : GridInitialPentagonBetween C.column C.turnRow x y) (r : GridRectangleBetween y x)
    (hleft : r.left = P.left) :
    P ∈ G.initialPentagons C x y ∧
        r ∈ (G.swapColumns C.column (finRotate n C.column)).unblockedRectangles y x ↔
      P.right = finRotate n (finRotate n C.column) ∧
        G.X C.column ∈ insert C.turnRow (Grid.cIco P.bottom C.turnRow) ∧
          G.X (finRotate n C.column) ∉ Grid.cIco P.bottom C.turnRow := by
  constructor
  · rintro ⟨hP, hr⟩
    obtain ⟨heP, haP⟩ := (G.mem_initialPentagons P).1 hP
    obtain ⟨her, har⟩ :=
      ((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles r).1 hr
    have hthin :=
      (P.toGridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
        r hleft).1 ⟨heP, her⟩
    rw [P.left_eq] at hthin
    exact ⟨hthin,
      (P.disjoint_pointSet_swapColumns_iff_of_rectangle_same_side_order r G.X hleft hthin).1
        ⟨haP, har⟩⟩
  · rintro ⟨hthin, hX⟩
    have hempty :=
      (P.toGridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
        r hleft).2 (by simpa only [P.left_eq] using hthin)
    have havoid :=
      (P.disjoint_pointSet_swapColumns_iff_of_rectangle_same_side_order r G.X hleft hthin).2 hX
    exact ⟨(G.mem_initialPentagons P).2 ⟨hempty.1, havoid.1⟩,
      ((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles r).2
        ⟨hempty.2, havoid.2⟩⟩

end GridDiagram

end TauCeti
