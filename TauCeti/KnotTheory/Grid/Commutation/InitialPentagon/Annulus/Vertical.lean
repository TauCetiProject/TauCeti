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

The exact marking tests apply to any grid state, hence to both `O`- and `X`-markings. They
characterize the counted vertical initial-side terms in the diagonal chain-map equation, without
assuming emptiness or `X`-avoidance as extra hypotheses.

## Main results

* `GridDiagram.mem_rectangleInitialPentagonSameSideOrder_iff_markings` and
  `GridDiagram.mem_initialPentagonRectangleSameSideOrder_iff_markings`: exact membership tests
  for the counted vertical initial-side terms.

## References

Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6.

This file adapts the terminal-side formalization in
`TauCeti.KnotTheory.Grid.Commutation.Annulus.Vertical`.
-/

public section

namespace TauCeti

namespace GridInitialPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- An initial-side pentagon spanning one column covers only squares in the two commuted
columns. -/
private theorem coveredSquares_eq_of_right_eq_finRotate_finRotate
    (P : GridInitialPentagonBetween a s x y) (hright : P.right = finRotate n (finRotate n a)) :
    P.coveredSquares =
      ({a} ×ˢ Grid.cIoo s P.top) ∪ ({finRotate n a} ×ˢ Grid.cIco P.bottom s) := by
  have hcols : Grid.cIco (finRotate n a) P.right = {finRotate n a} :=
    Grid.cIco_eq_singleton_iff.2 ⟨rfl, hright, P.right_ne.symm⟩
  ext p
  simp only [P.mem_coveredSquares, hcols, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton]
  grind

end GridInitialPentagonBetween

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- In a thin vertical rectangle--initial-side pentagon annulus, the pentagon's terminal side is
two columns after the first commuted column. -/
private theorem pentagon_right_eq_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    D.pentagon.right = finRotate n (finRotate n a) := by
  rw [pentagon_toGridRectangleBetween,
    D.first.right_eq_right_of_left_eq_left D.second hleft.symm, hthin, hleft, D.second_left_eq]

/-- In a thin vertical rectangle--initial-side pentagon annulus, the rectangle covers the
pentagon's complementary row arc in the second commuted column. -/
private theorem first_coveredSquares_eq_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    D.first.toGridRectangle.coveredSquares =
      {finRotate n a} ×ˢ Grid.cIco D.pentagon.top D.pentagon.bottom := by
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    rw [← D.pentagon_right_eq_of_same_side_order hleft hthin]
    exact D.pentagon.right_ne.symm
  rw [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
    GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, hthin, hleft, D.second_left_eq,
    Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩, pentagon_toGridRectangleBetween,
    D.first.bottom_eq_top_of_left_eq_left D.second hleft.symm,
    D.first.top_eq_bottom_of_left_eq_left D.second hleft.symm]

/-- A thin vertical rectangle--initial-side pentagon annulus covers complementary row arcs in
the two columns adjacent to the replaced line. -/
theorem coveredSquares_union_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    D.first.toGridRectangle.coveredSquares ∪ D.pentagon.coveredSquares =
      ({a} ×ˢ Grid.cIoo s D.pentagon.top) ∪
        ({finRotate n a} ×ˢ Grid.cIco D.pentagon.top s) := by
  have hcut : Grid.cIco D.pentagon.top D.pentagon.bottom ∪
      Grid.cIco D.pentagon.bottom s = Grid.cIco D.pentagon.top s := by
    by_cases hs : s = D.pentagon.bottom
    · simp [hs]
    · exact Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo
        (Grid.mem_cIoo_cyclic_right
          (Grid.mem_cIoo_of_mem_cIco D.pentagon.turn_mem_cIco_bottom_top hs))
  rw [D.first_coveredSquares_eq_of_same_side_order hleft hthin,
    D.pentagon.coveredSquares_eq_of_right_eq_finRotate_finRotate
      (D.pentagon_right_eq_of_same_side_order hleft hthin),
    Finset.union_left_comm, ← Finset.product_union, hcut]

/-- The two pieces of a thin vertical rectangle--initial-side pentagon annulus cover disjoint
squares. -/
theorem disjoint_coveredSquares_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    Disjoint D.first.toGridRectangle.coveredSquares D.pentagon.coveredSquares := by
  rw [D.first_coveredSquares_eq_of_same_side_order hleft hthin,
    D.pentagon.coveredSquares_eq_of_right_eq_finRotate_finRotate
      (D.pentagon_right_eq_of_same_side_order hleft hthin),
    Finset.disjoint_union_right, Finset.disjoint_product, Finset.disjoint_product,
    Finset.disjoint_singleton]
  refine ⟨Or.inl D.pentagon.ne_finRotate.symm, Or.inr ?_⟩
  by_cases hs : s = D.pentagon.bottom
  · simp [hs]
  · exact Finset.disjoint_left.2 fun t htop hbottom =>
      Finset.disjoint_left.mp (Grid.disjoint_cIco_swap D.pentagon.top D.pentagon.bottom) htop
        (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hbottom
          (Grid.mem_cIoo_of_mem_cIco D.pentagon.turn_mem_cIco_bottom_top hs))

/-- Avoiding any marking state in a thin vertical rectangle--initial-side pentagon annulus
amounts to placing the first commuted column's marking outside the pentagon's open arc and the
second commuted column's marking outside its covered half-open arc. -/
theorem disjoint_pointSet_iff_of_same_side_order
    (D : GridRectangleInitialPentagonDecomposition a s x x) (M : GridState n)
    (hleft : D.first.left = D.second.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    Disjoint D.first.toGridRectangle.coveredSquares M.pointSet ∧
        Disjoint D.pentagon.coveredSquares M.pointSet ↔
      M a ∉ Grid.cIoo s D.pentagon.top ∧
        M (finRotate n a) ∉ Grid.cIco D.pentagon.top s := by
  rw [← Finset.disjoint_union_left, D.coveredSquares_union_of_same_side_order hleft hthin,
    Finset.disjoint_union_left, M.disjoint_product_pointSet_iff,
    M.disjoint_product_pointSet_iff]
  simp only [Finset.mem_singleton, forall_eq]

end GridRectangleInitialPentagonDecomposition

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- In a thin vertical initial-side pentagon--rectangle annulus, the pentagon's terminal side is
two columns after the first commuted column. -/
private theorem pentagon_right_eq_of_same_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x)
    (hthin : D.first.right = finRotate n D.first.left) :
    D.pentagon.right = finRotate n (finRotate n a) := by
  rw [pentagon_toGridRectangleBetween, hthin, D.first_left_eq]

/-- In a thin vertical initial-side pentagon--rectangle annulus, the rectangle covers the
pentagon's complementary row arc in the second commuted column. -/
private theorem second_coveredSquares_eq_of_same_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x)
    (hleft : D.second.left = D.first.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    D.second.toGridRectangle.coveredSquares =
      {finRotate n a} ×ˢ Grid.cIco D.pentagon.top D.pentagon.bottom := by
  have hne : finRotate n a ≠ finRotate n (finRotate n a) := by
    rw [← D.pentagon_right_eq_of_same_side_order hthin]
    exact D.pentagon.right_ne.symm
  rw [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
    GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, hleft,
    D.first.right_eq_right_of_left_eq_left D.second hleft, hthin, D.first_left_eq,
    Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, hne⟩, pentagon_toGridRectangleBetween,
    D.first.bottom_eq_top_of_left_eq_left D.second hleft,
    D.first.top_eq_bottom_of_left_eq_left D.second hleft]

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
  rw [D.pentagon.coveredSquares_eq_of_right_eq_finRotate_finRotate
      (D.pentagon_right_eq_of_same_side_order hthin),
    D.second_coveredSquares_eq_of_same_side_order hleft hthin]
  ext p
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply,
    Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
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
  rw [D.pentagon.coveredSquares_eq_of_right_eq_finRotate_finRotate
      (D.pentagon_right_eq_of_same_side_order hthin),
    Finset.mem_union, Finset.mem_product, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_singleton] at hP
  rw [D.second_coveredSquares_eq_of_same_side_order hleft hthin, Finset.mem_map_equiv,
    Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm, Equiv.prodCongr_apply,
    Prod.map_apply', Finset.mem_product, Finset.mem_singleton, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_right, Equiv.refl_apply] at hr
  rcases hP with hP | hP
  · exact Finset.disjoint_left.mp
      (Grid.disjoint_cIco_swap D.pentagon.bottom D.pentagon.top)
        (Grid.insert_cIco_subset_cIco D.pentagon.turn_mem_cIco_bottom_top hP.2
          (Finset.mem_insert_self _ _)) hr.2
  · exact D.pentagon.ne_finRotate (hr.1.symm.trans hP.1)

/-- The marking test for a thin vertical initial-side pentagon--rectangle annulus, testing the
pentagon in the original marking state and the rectangle in the commuted marking state. -/
theorem disjoint_pointSet_swapColumns_iff_of_same_side_order
    (D : GridInitialPentagonRectangleDecomposition a s x x) (M : GridState n)
    (hleft : D.second.left = D.first.left)
    (hthin : D.first.right = finRotate n D.first.left) :
    Disjoint D.pentagon.coveredSquares M.pointSet ∧
        Disjoint D.second.toGridRectangle.coveredSquares
          (M.swapColumns a (finRotate n a)).pointSet ↔
      M a ∈ insert s (Grid.cIco D.pentagon.bottom s) ∧
        M (finRotate n a) ∉ Grid.cIco D.pentagon.bottom s := by
  rw [GridState.swapColumns,
    ← M.disjoint_map_relabelColumns_pointSet_iff (Equiv.swap a (finRotate n a)),
    Equiv.symm_swap, ← Finset.disjoint_union_left,
    D.coveredSquares_union_map_of_same_side_order hleft hthin,
    Finset.disjoint_union_left, M.disjoint_product_pointSet_iff,
    M.disjoint_product_pointSet_iff]
  simp only [Finset.mem_singleton, forall_eq, Finset.mem_sdiff, Finset.mem_univ,
    true_and, not_not]

end GridInitialPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- An exact characterization of the counted vertical rectangle--initial-side pentagon terms.
Thinness implies emptiness of both domains, leaving just the two `X`-marking tests. -/
theorem mem_rectangleInitialPentagonSameSideOrder_iff_markings (x : GridState n)
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x) :
    D ∈ G.rectangleInitialPentagonSameSideOrder C x ↔
      D.first.left = D.second.left ∧ D.first.right = finRotate n D.first.left ∧
        G.X C.column ∉ Grid.cIoo C.turnRow D.pentagon.top ∧
          G.X (finRotate n C.column) ∉ Grid.cIco D.pentagon.top C.turnRow := by
  constructor
  · intro hD
    obtain ⟨hcount, hleft, -⟩ := (G.mem_rectangleInitialPentagonSameSideOrder C x D).1 hD
    have hthin :=
      G.rectangle_right_eq_finRotate_left_of_mem_rectangleInitialPentagonSameSideOrder C x D hD
    obtain ⟨hr, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcount
    exact ⟨hleft, hthin, (D.disjoint_pointSet_iff_of_same_side_order G.X hleft hthin).1
      ⟨((G.mem_unblockedRectangles _).1 hr).2, ((G.mem_initialPentagons _).1 hP).2⟩⟩
  · rintro ⟨hleft, hthin, hX⟩
    have hempty := (D.first.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
      D.second hleft.symm).2 hthin
    have havoid := (D.disjoint_pointSet_iff_of_same_side_order G.X hleft hthin).2 hX
    exact (G.mem_rectangleInitialPentagonSameSideOrder C x D).2
      ⟨(G.mem_rectangleInitialPentagonDecompositions C D).2
        ⟨(G.mem_unblockedRectangles _).2 ⟨hempty.1, havoid.1⟩,
          (G.mem_initialPentagons _).2 ⟨by
            simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
              using hempty.2, havoid.2⟩⟩,
        hleft, (D.first.right_eq_right_of_left_eq_left D.second hleft.symm).symm⟩

/-- An exact characterization of the counted vertical initial-side pentagon--rectangle terms,
with the rectangle's `X`-markings read in the commuted diagram. -/
theorem mem_initialPentagonRectangleSameSideOrder_iff_markings (x : GridState n)
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x) :
    D ∈ G.initialPentagonRectangleSameSideOrder C x ↔
      D.second.left = D.first.left ∧ D.first.right = finRotate n D.first.left ∧
        G.X C.column ∈ insert C.turnRow (Grid.cIco D.pentagon.bottom C.turnRow) ∧
          G.X (finRotate n C.column) ∉ Grid.cIco D.pentagon.bottom C.turnRow := by
  constructor
  · intro hD
    obtain ⟨hcount, hleft, -⟩ := (G.mem_initialPentagonRectangleSameSideOrder C x D).1 hD
    have hthin :=
      G.pentagon_right_eq_finRotate_left_of_mem_initialPentagonRectangleSameSideOrder C x D hD
    obtain ⟨hP, hr⟩ := (G.mem_initialPentagonRectangleDecompositions C D).1 hcount
    exact ⟨hleft, hthin,
      (D.disjoint_pointSet_swapColumns_iff_of_same_side_order G.X hleft hthin).1
        ⟨((G.mem_initialPentagons _).1 hP).2,
          (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1
            hr).2⟩⟩
  · rintro ⟨hleft, hthin, hX⟩
    have hempty := (D.first.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
      D.second hleft).2 hthin
    have havoid := (D.disjoint_pointSet_swapColumns_iff_of_same_side_order G.X hleft hthin).2 hX
    exact (G.mem_initialPentagonRectangleSameSideOrder C x D).2
      ⟨(G.mem_initialPentagonRectangleDecompositions C D).2
        ⟨(G.mem_initialPentagons _).2 ⟨by
            simpa only [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
              using hempty.1, havoid.1⟩,
          ((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).2
            ⟨hempty.2, havoid.2⟩⟩,
        hleft, D.first.right_eq_right_of_left_eq_left D.second hleft⟩

end GridDiagram

end TauCeti
