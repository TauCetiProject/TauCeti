/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Empty

/-!
# Markings in vertical commutation annuli

A thin vertical rectangle--pentagon annulus covers two parts of the columns adjacent to
the replaced grid line. In the first column it covers every row except the arc from the
pentagon's bottom to its turn, including the turn itself. In the second column it covers
that half-open arc, excluding the turn. For the opposite composition order, the rectangle
must be read back in the original columns; the corresponding cut is at the pentagon's top.

The exact marking tests below apply to any grid state, hence to both O- and X-markings.
They characterize the counted vertical terms in the diagonal pentagon chain-map equation,
without assuming emptiness or X-avoidance as extra hypotheses.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1,
Case (P-3), Figures 5.5--5.6.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- The squares covered by a thin vertical rectangle--pentagon annulus, in the original
columns. The turn row is missing from both columns. -/
theorem coveredSquares_union_of_same_side_order
    (D : GridRectanglePentagonDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.left) (hthin : D.pentagon.left = a) :
    D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.coveredSquares =
      ({a} ×ˢ (Finset.univ \ insert s (Grid.cIco D.pentagon.bottom s))) ∪
        ({finRotate n a} ×ˢ Grid.cIco D.pentagon.bottom s) := by
  rw [D.pentagon.toGridRectangleBetween.coveredSquares_eq_product_of_left_eq_left
    D.rectangle hleft]
  have hcols : Grid.cIco a (finRotate n a) = {a} :=
    Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, D.pentagon.ne_finRotate⟩
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
  simp only [Finset.mem_union, hthin, D.pentagon.right_eq, hcols,
    D.pentagon.mem_coveredSquares, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  have := hrows p.2
  grind

/-- The constituent domains of a vertical rectangle--pentagon annulus cover disjoint
squares, so no O-marking contributes twice to its weight. -/
theorem disjoint_coveredSquares_of_same_side_order
    (D : GridRectanglePentagonDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.left) :
    Disjoint D.rectangle.toGridRectangle.coveredSquares D.pentagon.coveredSquares := by
  rw [D.pentagon.toGridRectangleBetween.coveredSquares_eq_product_of_left_eq_left
    D.rectangle hleft]
  exact (D.pentagon.disjoint_coveredSquares_of_forall_mem_cIco
    fun _ hp => (Finset.mem_product.1 hp).2).symm

/-- Avoiding any marking state in a thin vertical rectangle--pentagon annulus amounts to
placing the first column's marking in the omitted closed arc and the second column's
marking outside its covered half-open arc. -/
theorem disjoint_pointSet_iff_of_same_side_order
    (D : GridRectanglePentagonDecomposition a s x x) (M : GridState n)
    (hleft : D.rectangle.left = D.pentagon.left) (hthin : D.pentagon.left = a) :
    Disjoint D.rectangle.toGridRectangle.coveredSquares M.pointSet ∧
        Disjoint D.pentagon.coveredSquares M.pointSet ↔
      M a ∈ insert s (Grid.cIco D.pentagon.bottom s) ∧
        M (finRotate n a) ∉ Grid.cIco D.pentagon.bottom s := by
  rw [← Finset.disjoint_union_left, D.coveredSquares_union_of_same_side_order hleft hthin,
    Finset.disjoint_union_left, M.disjoint_product_pointSet_iff,
    M.disjoint_product_pointSet_iff]
  simp only [Finset.mem_singleton, forall_eq, Finset.mem_sdiff, Finset.mem_univ,
    true_and, not_not]

end GridRectanglePentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x : GridState n}

/-- The squares covered by a thin vertical pentagon--rectangle annulus after swapping
back the rectangle's columns. The turn row is missing from both columns. -/
theorem coveredSquares_union_map_of_same_side_order
    (D : GridPentagonRectangleDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.left) (hthin : D.pentagon.left = a) :
    D.pentagon.coveredSquares ∪ D.rectangle.toGridRectangle.coveredSquares.map
        ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding =
      ({a} ×ˢ Grid.cIoo s D.pentagon.top) ∪
        ({finRotate n a} ×ˢ Grid.cIco D.pentagon.top s) := by
  classical
  rw [D.pentagon.toGridRectangleBetween.coveredSquares_eq_product_of_left_eq_left
    D.rectangle hleft]
  have hcols : Grid.cIco a (finRotate n a) = {a} :=
    Grid.cIco_eq_singleton_iff.2 ⟨rfl, rfl, D.pentagon.ne_finRotate⟩
  have hrows (t : Fin n) :
      (t ∈ Grid.cIco D.pentagon.top D.pentagon.bottom ∨
        t ∈ Grid.cIco D.pentagon.bottom s) ↔ t ∈ Grid.cIco D.pentagon.top s := by
    have hcut : Grid.cIco D.pentagon.top D.pentagon.bottom ∪
        Grid.cIco D.pentagon.bottom s = Grid.cIco D.pentagon.top s := by
      by_cases hs : s = D.pentagon.bottom
      · simp [hs]
      · exact Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo
          (Grid.mem_cIoo_cyclic_right
            (Grid.mem_cIoo_of_mem_cIco D.pentagon.turn_mem_cIco_bottom_top hs))
    rw [← Finset.mem_union, hcut]
  ext p
  simp only [Finset.mem_union, Finset.mem_map_equiv, Equiv.prodCongr_symm,
    Equiv.symm_swap, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply',
    Equiv.refl_apply, hthin,
    D.pentagon.right_eq, hcols, D.pentagon.mem_coveredSquares,
    Finset.mem_product, Finset.mem_singleton, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_left]
  have := hrows p.2
  grind

/-- Reading the rectangle back in the original columns gives disjoint constituent domains
for a vertical pentagon--rectangle annulus. -/
theorem disjoint_coveredSquares_map_of_same_side_order
    (D : GridPentagonRectangleDecomposition a s x x)
    (hleft : D.rectangle.left = D.pentagon.left) :
    Disjoint D.pentagon.coveredSquares (D.rectangle.toGridRectangle.coveredSquares.map
      ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding) := by
  rw [D.pentagon.toGridRectangleBetween.coveredSquares_eq_product_of_left_eq_left
    D.rectangle hleft]
  apply D.pentagon.disjoint_coveredSquares_of_forall_mem_cIco
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hp
  -- The commutation swap acts only on columns, so the row is unchanged.
  simpa only [Equiv.coe_toEmbedding, Equiv.prodCongr_apply, Prod.map_snd,
    Equiv.refl_apply] using (Finset.mem_product.1 hq).2

/-- The marking test for a thin vertical pentagon--rectangle annulus, testing the rectangle
in the commuted marking state and the pentagon in the original marking state. -/
theorem disjoint_pointSet_swapColumns_iff_of_same_side_order
    (D : GridPentagonRectangleDecomposition a s x x) (M : GridState n)
    (hleft : D.rectangle.left = D.pentagon.left) (hthin : D.pentagon.left = a) :
    Disjoint D.pentagon.coveredSquares M.pointSet ∧
        Disjoint D.rectangle.toGridRectangle.coveredSquares
          (M.swapColumns a (finRotate n a)).pointSet ↔
      M a ∉ Grid.cIoo s D.pentagon.top ∧
        M (finRotate n a) ∉ Grid.cIco D.pentagon.top s := by
  rw [GridState.swapColumns,
    ← M.disjoint_map_relabelColumns_pointSet_iff (Equiv.swap a (finRotate n a)),
    Equiv.symm_swap, ← Finset.disjoint_union_left,
    D.coveredSquares_union_map_of_same_side_order hleft hthin,
    Finset.disjoint_union_left, M.disjoint_product_pointSet_iff,
    M.disjoint_product_pointSet_iff]
  simp

end GridPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- An exact characterization of the counted vertical rectangle--pentagon terms. Thinness
implies emptiness of both domains, leaving just the two X-marking tests. -/
theorem mem_rectanglePentagonSameSideOrder_iff_markings (x : GridState n)
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x) :
    D ∈ G.rectanglePentagonSameSideOrder C x ↔
      D.rectangle.left = D.pentagon.left ∧ D.pentagon.left = C.column ∧
        G.X C.column ∈ insert C.turnRow (Grid.cIco D.pentagon.bottom C.turnRow) ∧
          G.X (finRotate n C.column) ∉ Grid.cIco D.pentagon.bottom C.turnRow := by
  constructor
  · intro hD
    obtain ⟨hcount, hleft, -⟩ := (G.mem_rectanglePentagonSameSideOrder C x D).1 hD
    have hthin := G.pentagon_left_eq_column_of_mem_rectanglePentagonSameSideOrder C x D hD
    obtain ⟨hr, hp⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcount
    refine ⟨hleft, hthin, ?_⟩
    exact (D.disjoint_pointSet_iff_of_same_side_order G.X hleft hthin).1
      ⟨((G.mem_unblockedRectangles _).1 hr).2, ((G.mem_pentagons _).1 hp).2⟩
  · rintro ⟨hleft, hthin, hX⟩
    have hright := D.pentagon.toGridRectangleBetween.right_eq_right_of_left_eq_left
      D.rectangle hleft
    have hempty := (D.rectangle.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
      D.pentagon.toGridRectangleBetween hleft.symm).2
        (by simpa only [hleft, hthin] using hright.trans D.pentagon.right_eq)
    have havoid := (D.disjoint_pointSet_iff_of_same_side_order G.X hleft hthin).2 hX
    apply (G.mem_rectanglePentagonSameSideOrder C x D).2
    exact ⟨(G.mem_rectanglePentagonDecompositions C D).2
      ⟨(G.mem_unblockedRectangles _).2 ⟨hempty.1, havoid.1⟩,
        (G.mem_pentagons _).2 ⟨hempty.2, havoid.2⟩⟩, hleft, hright⟩

/-- An exact characterization of the counted vertical pentagon--rectangle terms, with the
rectangle's X-markings read in the commuted diagram. -/
theorem mem_pentagonRectangleSameSideOrder_iff_markings (x : GridState n)
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x x) :
    D ∈ G.pentagonRectangleSameSideOrder C x ↔
      D.rectangle.left = D.pentagon.left ∧ D.pentagon.left = C.column ∧
        G.X C.column ∉ Grid.cIoo C.turnRow D.pentagon.top ∧
          G.X (finRotate n C.column) ∉ Grid.cIco D.pentagon.top C.turnRow := by
  constructor
  · intro hD
    obtain ⟨hcount, hleft, -⟩ := (G.mem_pentagonRectangleSameSideOrder C x D).1 hD
    have hthin := G.pentagon_left_eq_column_of_mem_pentagonRectangleSameSideOrder C x D hD
    obtain ⟨hp, hr⟩ := (G.mem_pentagonRectangleDecompositions C D).1 hcount
    refine ⟨hleft, hthin, ?_⟩
    exact (D.disjoint_pointSet_swapColumns_iff_of_same_side_order G.X hleft hthin).1
      ⟨((G.mem_pentagons _).1 hp).2,
        (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hr).2⟩
  · rintro ⟨hleft, hthin, hX⟩
    have hright := D.pentagon.toGridRectangleBetween.right_eq_right_of_left_eq_left
      D.rectangle hleft
    have hempty :=
      (GridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
        D.pentagon.toGridRectangleBetween D.rectangle hleft).2
          (D.pentagon.right_eq.trans (congrArg (finRotate n) hthin).symm)
    have havoid := (D.disjoint_pointSet_swapColumns_iff_of_same_side_order G.X hleft hthin).2 hX
    apply (G.mem_pentagonRectangleSameSideOrder C x D).2
    exact ⟨(G.mem_pentagonRectangleDecompositions C D).2
      ⟨(G.mem_pentagons _).2 ⟨hempty.1, havoid.1⟩,
        ((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).2
          ⟨hempty.2, havoid.2⟩⟩, hleft, hright⟩

end GridDiagram

end TauCeti
