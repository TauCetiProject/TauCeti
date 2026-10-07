/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Empty

/-!
# Markings in vertical initial-side commutation annuli

A thin vertical annulus involving an initial-side pentagon is supported in the two columns
adjacent to the replaced grid line. This file identifies its covered squares in both composition
orders. The formulas make the two pieces disjoint and expose exactly which `O`- and `X`-markings
can occur in their composite weights.

## References

Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6.
-/

public section

namespace TauCeti

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- A thin vertical rectangle--initial-side pentagon annulus covers complementary row arcs in
the two columns adjacent to the replaced line. -/
theorem coveredSquares_union_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    D.first.toGridRectangle.coveredSquares ∪ D.pentagon.coveredSquares =
      ({a} ×ˢ Grid.cIoo s D.pentagon.top) ∪
        ({finRotate n a} ×ˢ Grid.cIco D.pentagon.top s) := by
  have hfirstLeft : D.first.left = finRotate n a := hleft.trans D.second_left_eq
  have hright := D.first.right_eq_right_of_left_eq_left D.second hleft.symm
  have hbottom := D.first.bottom_eq_top_of_left_eq_left D.second hleft.symm
  have htop := D.first.top_eq_bottom_of_left_eq_left D.second hleft.symm
  have hpBottom : D.pentagon.bottom = D.first.top := by
    rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
    exact hbottom
  have hpTop : D.pentagon.top = D.first.bottom := by
    rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
    exact htop
  have hpRight : D.pentagon.right = finRotate n (finRotate n a) := by
    rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
    exact hright.trans (hthin.trans (congrArg (finRotate n) hfirstLeft))
  have hcols : Grid.cIco (finRotate n a) D.pentagon.right = {finRotate n a} :=
    Grid.cIco_eq_singleton_iff.2
      ⟨rfl, hpRight, by simpa only [D.pentagon.left_eq] using D.pentagon.left_ne_right⟩
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    intro h
    exact D.first.left_ne_right
      (hfirstLeft.trans (h.trans ((congrArg (finRotate n) hfirstLeft).symm.trans hthin.symm)))
  have hfirstCols : Grid.cIco D.first.left D.first.right = {finRotate n a} := by
    rw [hfirstLeft, hthin, hfirstLeft]
    exact Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩
  have hrows (t : Fin n) :
      (t ∈ Grid.cIco D.pentagon.top D.pentagon.bottom ∨
        t ∈ Grid.cIco D.pentagon.bottom s) ↔
          t ∈ Grid.cIco D.pentagon.top s := by
    have hcut : Grid.cIco D.pentagon.top D.pentagon.bottom ∪
        Grid.cIco D.pentagon.bottom s = Grid.cIco D.pentagon.top s := by
      by_cases hs : s = D.pentagon.bottom
      · simp [hs]
      · exact Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo
          (Grid.mem_cIoo_cyclic_right
            (Grid.mem_cIoo_of_mem_cIco D.pentagon.turn_mem_cIco_bottom_top hs))
    rw [← Finset.mem_union, hcut]
  ext p
  simp only [Finset.mem_union, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    hfirstCols, hcols, D.pentagon.mem_coveredSquares,
    Finset.mem_product, Finset.mem_singleton]
  simp only [← hpBottom, ← hpTop]
  have := hrows p.2
  grind

/-- The two pieces of a thin vertical rectangle--initial-side pentagon annulus cover disjoint
squares. -/
theorem disjoint_coveredSquares_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    Disjoint D.first.toGridRectangle.coveredSquares D.pentagon.coveredSquares := by
  rw [Finset.disjoint_left]
  intro p hp hP
  have hfirstLeft : D.first.left = finRotate n a := hleft.trans D.second_left_eq
  have hright := D.first.right_eq_right_of_left_eq_left D.second hleft.symm
  have hbottom := D.first.bottom_eq_top_of_left_eq_left D.second hleft.symm
  have htop := D.first.top_eq_bottom_of_left_eq_left D.second hleft.symm
  have hpBottom : D.pentagon.bottom = D.first.top := by
    rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
    exact hbottom
  have hpTop : D.pentagon.top = D.first.bottom := by
    rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
    exact htop
  have hpRight : D.pentagon.right = finRotate n (finRotate n a) := by
    rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
    exact hright.trans (hthin.trans (congrArg (finRotate n) hfirstLeft))
  have hcols : Grid.cIco (finRotate n a) D.pentagon.right = {finRotate n a} :=
    Grid.cIco_eq_singleton_iff.2
      ⟨rfl, hpRight, by simpa only [D.pentagon.left_eq] using D.pentagon.left_ne_right⟩
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    intro h
    exact D.first.left_ne_right
      (hfirstLeft.trans (h.trans ((congrArg (finRotate n) hfirstLeft).symm.trans hthin.symm)))
  have hfirstCols : Grid.cIco D.first.left D.first.right = {finRotate n a} := by
    rw [hfirstLeft, hthin, hfirstLeft]
    exact Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩
  rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, hfirstCols,
    Finset.mem_singleton, ← hpBottom, ← hpTop] at hp
  rw [D.pentagon.mem_coveredSquares, hcols] at hP
  rcases hP with hP | hP | hP
  · exact hP.1 (Finset.mem_singleton.mp hP.2.1)
  · exact D.pentagon.ne_finRotate (hP.1.symm.trans hp.1)
  · have hrow : p.2 ∈ Grid.cIco D.pentagon.bottom D.pentagon.top := by
      by_cases hs : s = D.pentagon.bottom
      · simp [hs] at hP
      · exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hP.2
          (Grid.mem_cIoo_of_mem_cIco D.pentagon.turn_mem_cIco_bottom_top hs)
    exact Finset.disjoint_left.mp
      (Grid.disjoint_cIco_swap D.pentagon.top D.pentagon.bottom) hp.2 hrow

end GridRectangleInitialPentagonDecomposition

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- After the rectangle is read in the original columns, a thin vertical initial-side
pentagon--rectangle annulus covers complementary row arcs in the two commuted columns. -/
theorem coveredSquares_union_map_of_same_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x)
    (hleft : D.second.left = D.first.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    D.pentagon.coveredSquares ∪ D.second.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      ({a} ×ˢ (Finset.univ \ insert s (Grid.cIco D.pentagon.bottom s))) ∪
        ({finRotate n a} ×ˢ Grid.cIco D.pentagon.bottom s) := by
  classical
  have hfirstLeft : D.first.left = finRotate n a := D.first_left_eq
  have hright := D.first.right_eq_right_of_left_eq_left D.second hleft
  have hbottom := D.first.bottom_eq_top_of_left_eq_left D.second hleft
  have htop := D.first.top_eq_bottom_of_left_eq_left D.second hleft
  have hpBottom : D.pentagon.bottom = D.first.bottom := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
  have hpTop : D.pentagon.top = D.first.top := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
  have hpRight : D.pentagon.right = finRotate n (finRotate n a) := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
    exact hthin.trans (congrArg (finRotate n) hfirstLeft)
  have hcols : Grid.cIco (finRotate n a) D.pentagon.right = {finRotate n a} :=
    Grid.cIco_eq_singleton_iff.2
      ⟨rfl, hpRight, by simpa only [D.pentagon.left_eq] using D.pentagon.left_ne_right⟩
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    intro h
    exact D.first.left_ne_right
      (hfirstLeft.trans (h.trans ((congrArg (finRotate n) hfirstLeft).symm.trans hthin.symm)))
  have hsecondCols : Grid.cIco D.second.left D.second.right = {finRotate n a} := by
    rw [hleft, hright, hfirstLeft, hthin, hfirstLeft]
    exact Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩
  have hrows (t : Fin n) :
      (t ∈ Grid.cIco D.pentagon.top D.pentagon.bottom ∨
        t ∈ Grid.cIoo s D.pentagon.top) ↔
          t ∉ insert s (Grid.cIco D.pentagon.bottom s) := by
    have hsplit := Grid.ite_mem_cIco_eq_add_add D.pentagon.turn_mem_cIco_bottom_top t
    have hcover : t ∈ Grid.cIco D.pentagon.bottom D.pentagon.top ∨
        t ∈ Grid.cIco D.pentagon.top D.pentagon.bottom := by
      rw [← Finset.mem_union, Grid.cIco_union_swap D.pentagon.bottom_ne_top]
      exact Finset.mem_univ t
    have hdisjoint := Finset.disjoint_left.mp
      (Grid.disjoint_cIco_swap D.pentagon.bottom D.pentagon.top)
    simp only [Finset.mem_insert]
    split_ifs at hsplit <;> grind
  ext p
  simp only [Finset.mem_union, D.pentagon.mem_coveredSquares, hcols,
    Finset.mem_product, Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, hsecondCols,
    hbottom.trans hpTop.symm, htop.trans hpBottom.symm]
  have := hrows p.2
  grind

/-- The initial-side pentagon and the rectangle read back in the original columns cover
disjoint squares in a thin vertical annulus. -/
theorem disjoint_coveredSquares_map_of_same_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x)
    (hleft : D.second.left = D.first.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    Disjoint D.pentagon.coveredSquares
      (D.second.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding) := by
  classical
  rw [Finset.disjoint_left]
  intro p hP hr
  have hfirstLeft : D.first.left = finRotate n a := D.first_left_eq
  have hright := D.first.right_eq_right_of_left_eq_left D.second hleft
  have hbottom := D.first.bottom_eq_top_of_left_eq_left D.second hleft
  have htop := D.first.top_eq_bottom_of_left_eq_left D.second hleft
  have hpBottom : D.pentagon.bottom = D.first.bottom := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
  have hpTop : D.pentagon.top = D.first.top := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
  have hpRight : D.pentagon.right = finRotate n (finRotate n a) := by
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
    exact hthin.trans (congrArg (finRotate n) hfirstLeft)
  have hcols : Grid.cIco (finRotate n a) D.pentagon.right = {finRotate n a} :=
    Grid.cIco_eq_singleton_iff.2
      ⟨rfl, hpRight, by simpa only [D.pentagon.left_eq] using D.pentagon.left_ne_right⟩
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    intro h
    exact D.first.left_ne_right
      (hfirstLeft.trans (h.trans ((congrArg (finRotate n) hfirstLeft).symm.trans hthin.symm)))
  have hsecondCols : Grid.cIco D.second.left D.second.right = {finRotate n a} := by
    rw [hleft, hright, hfirstLeft, hthin, hfirstLeft]
    exact Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩
  rw [D.pentagon.mem_coveredSquares, hcols] at hP
  rw [Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply, Prod.map_apply', Prod.fst, Prod.snd, Equiv.refl_apply,
    GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, hsecondCols,
    hbottom.trans hpTop.symm, htop.trans hpBottom.symm] at hr
  have hpcol : p.1 = a := by
    have hswap := Finset.mem_singleton.mp hr.1
    simpa only [Equiv.swap_apply_self, Equiv.swap_apply_right] using
      congrArg (Equiv.swap a (finRotate n a)) hswap
  rcases hP with hP | hP | hP
  · exact hP.1 (Finset.mem_singleton.mp hP.2.1)
  · exact Finset.disjoint_left.mp
      (Grid.disjoint_cIco_swap D.pentagon.bottom D.pentagon.top)
        (Grid.insert_cIco_subset_cIco D.pentagon.turn_mem_cIco_bottom_top hP.2
          (Finset.mem_insert_self _ _)) hr.2
  · exact D.pentagon.ne_finRotate (hpcol.symm.trans hP.1)

end GridInitialPentagonRectangleDecomposition

end TauCeti
