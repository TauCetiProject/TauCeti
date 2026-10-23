/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Recut

/-!
# Recutting pairs of initial-side commutation pentagons

Two empty pentagons turning on the initial side of the replaced grid line share that side.
Their distinct terminal sides have two possible cyclic orders. When the second lies inside the
first column interval, the recut is an initial-side hexagon followed by a rectangle; in the
complementary order it is a rectangle followed by an initial-side hexagon. The two turn rows occur
in the required order on either hexagon.

If the pentagons avoid the `X`-markings in the forward and reverse diagrams, both recuts are
counted and have no counted hexagon-composite recut partner. These are the two initial--initial
geometric cases in the matching between unpaired hexagon composites and pentagon pairs in the
commutation homotopy equation. No homotopy equation or weight identity is asserted here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.1, Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti
namespace GridInitialPentagonBetween

variable {n : ℕ} {a s t : Fin n} {x y z : GridState n}

private theorem pair_turn_order (P : GridInitialPentagonBetween a s x y)
    (Q : GridInitialPentagonBetween a t y z)
    (hright : P.right ≠ Q.right) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    (s ∈ Grid.cIco P.bottom Q.top ∧ t ∈ Grid.cIoo s Q.top) ∧
      t ∉ Grid.cIoo s P.top ∧ s ∉ Grid.cIco Q.bottom Q.top := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hrow := (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    hright hP hQ).2
  have hbottom := D.second_bottom_eq_first_top_of_left_eq_left hcommon
  have hs := P.turn_mem_cIco_bottom_top
  have ht := Q.turn_mem_cIco_bottom_top
  simp only [D] at hrow hbottom
  rw [hbottom] at ht ⊢
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hrow hs ht ⊢
  split_ifs at hrow hs ht ⊢ <;> omega

/-- Recut two empty initial-side pentagons into an initial-side hexagon followed by a
rectangle, when the second terminal side is inside the first column interval. -/
noncomputable def recutHexagonRectangle (P : GridInitialPentagonBetween a s x y)
    (Q : GridInitialPentagonBetween a t y z)
    (hcol : Q.right ∈ Grid.cIoo (finRotate n a) P.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) : GridHexagonRectangleDecomposition a s t x z := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.second.right ∈ Grid.cIoo D.first.left D.first.right := P.left_eq ▸ hcol
  let E := D.recut (D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hc) hP hQ
  have hsides := D.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hc hP hQ
  have hrows := D.recut_first_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hc hP hQ
  have hbottom : E.first.bottom = P.bottom := hrows.1
  have htop : E.first.top = Q.top := hrows.2
  have hturns := (P.pair_turn_order Q (Grid.ne_right_of_mem_cIoo hcol).symm hP hQ).1
  exact ⟨E.middle, Sum.inr ⟨E.first, hsides.1.trans P.left_eq,
    by simpa only [← E.first.bottom_def, ← E.first.top_def, hbottom, htop] using hturns.1,
    by simpa only [← E.first.top_def, htop] using hturns.2⟩, E.second⟩

/-- Forgetting the hexagon turns returns the canonical empty-rectangle recut. -/
@[simp]
theorem recutHexagonRectangle_toRectangleDecomposition
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a t y z)
    (hcol : Q.right ∈ Grid.cIoo (finRotate n a) P.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    (P.recutHexagonRectangle Q hcol hP hQ).toRectangleDecomposition =
      GridRectangleDecomposition.recut
        (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
          GridRectangleDecomposition x z)
        (GridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo _
          (P.left_eq.trans Q.left_eq.symm) (P.left_eq ▸ hcol)) hP hQ := by
  simp only [recutHexagonRectangle, GridHexagonRectangleDecomposition.toRectangleDecomposition,
    GridCommutationHexagonBetween.toGridRectangleBetween_inr]

/-- The hexagon--rectangle composite is an empty-rectangle recut of the pentagon pair. -/
theorem isRecut_recutHexagonRectangle
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a t y z)
    (hcol : Q.right ∈ Grid.cIoo (finRotate n a) P.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecut
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z)
      (P.recutHexagonRectangle Q hcol hP hQ).toRectangleDecomposition := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.second.right ∈ Grid.cIoo D.first.left D.first.right := P.left_eq ▸ hcol
  let hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hc
  have hF : (P.recutHexagonRectangle Q hcol hP hQ).toRectangleDecomposition =
      D.recut hone hP hQ := P.recutHexagonRectangle_toRectangleDecomposition Q hcol hP hQ
  exact hF.symm ▸ D.isRecut_recut hone hP hQ

/-- The recut hexagon turns on its initial side. -/
@[simp]
theorem recutHexagonRectangle_hexagon_isLeft
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a t y z)
    (hcol : Q.right ∈ Grid.cIoo (finRotate n a) P.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    (P.recutHexagonRectangle Q hcol hP hQ).hexagon.isLeft = false := (rfl)

/-- Recut two empty initial-side pentagons into a rectangle followed by an initial-side
hexagon, when the first terminal side is inside the second column interval. -/
noncomputable def recutRectangleHexagon (P : GridInitialPentagonBetween a s x y)
    (Q : GridInitialPentagonBetween a t y z)
    (hcol : P.right ∈ Grid.cIoo (finRotate n a) Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) : GridRectangleHexagonDecomposition a s t x z := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.first.right ∈ Grid.cIoo D.first.left D.second.right := P.left_eq ▸ hcol
  let E := D.recut (D.hasOneCommonSide_of_left_eq_left hcommon
    (Grid.ne_right_of_mem_cIoo hc)) hP hQ
  have hsides := D.recut_sides_of_left_eq_left_of_first_right_mem_cIoo
    hcommon hc hP hQ
  have hrows := D.recut_second_bottom_top_of_left_eq_left_of_first_right_mem_cIoo
    hcommon hc hP hQ
  have hbottom : E.second.bottom = P.bottom := by
    dsimp only [E]
    exact hrows.1
  have htop : E.second.top = Q.top := by
    dsimp only [E]
    exact hrows.2
  have hturns := (P.pair_turn_order Q (Grid.ne_right_of_mem_cIoo hcol) hP hQ).1
  exact ⟨E.middle, E.first, Sum.inr ⟨E.second, hsides.2.2.1.trans P.left_eq,
    by simpa only [← E.second.bottom_def, ← E.second.top_def, hbottom, htop]
      using hturns.1,
    by simpa only [← E.second.top_def, htop] using hturns.2⟩⟩

/-- Forgetting the hexagon turns returns the canonical empty-rectangle recut. -/
@[simp]
theorem recutRectangleHexagon_toRectangleDecomposition
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a t y z)
    (hcol : P.right ∈ Grid.cIoo (finRotate n a) Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    (P.recutRectangleHexagon Q hcol hP hQ).toRectangleDecomposition =
      GridRectangleDecomposition.recut
        (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
          GridRectangleDecomposition x z)
        (GridRectangleDecomposition.hasOneCommonSide_of_left_eq_left _
          (P.left_eq.trans Q.left_eq.symm) (Grid.ne_right_of_mem_cIoo (P.left_eq ▸ hcol)))
        hP hQ := by
  simp only [recutRectangleHexagon,
    GridRectangleHexagonDecomposition.toRectangleDecomposition,
    GridCommutationHexagonBetween.toGridRectangleBetween_inr]

/-- The rectangle--hexagon composite is an empty-rectangle recut of the pentagon pair. -/
theorem isRecut_recutRectangleHexagon
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a t y z)
    (hcol : P.right ∈ Grid.cIoo (finRotate n a) Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecut
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z)
      (P.recutRectangleHexagon Q hcol hP hQ).toRectangleDecomposition := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.first.right ∈ Grid.cIoo D.first.left D.second.right := P.left_eq ▸ hcol
  let hone := D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hc)
  have hF : (P.recutRectangleHexagon Q hcol hP hQ).toRectangleDecomposition =
      D.recut hone hP hQ := P.recutRectangleHexagon_toRectangleDecomposition Q hcol hP hQ
  exact hF.symm ▸ D.isRecut_recut hone hP hQ

/-- The hexagon in the complementary recut turns on its initial side. -/
@[simp]
theorem recutRectangleHexagon_hexagon_isLeft
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a t y z)
    (hcol : P.right ∈ Grid.cIoo (finRotate n a) Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    (P.recutRectangleHexagon Q hcol hP hQ).hexagon.isLeft = false := (rfl)

end GridInitialPentagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

private theorem initialPair_notMem_XSet_away {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridInitialPentagonBetween C.column C.oppositeTurnRow y z)
    (hP : Disjoint P.coveredSquares G.XSet)
    (hQ : Disjoint Q.coveredSquares
      (G.swapColumns C.column (finRotate n C.column)).XSet)
    {p : Fin n × Fin n} (ha : p.1 ≠ C.column) (hb : p.1 ≠ finRotate n C.column)
    (hp : p ∈ P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares) :
    p ∉ G.XSet := by
  intro hX
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.disjoint_left.mp hP
      ((P.mem_coveredSquares_iff_of_ne ha hb).mpr hp) hX
  · apply Finset.disjoint_left.mp hQ ((Q.mem_coveredSquares_iff_of_ne ha hb).mpr hp)
    simpa only [G.mem_XSet_swapColumns, Equiv.swap_apply_of_ne_of_ne ha hb] using hX

/-- The initial-side pentagon recut is a counted hexagon--rectangle composite when the
forward pentagon and the reverse pentagon avoid their respective `X`-markings. -/
theorem recutHexagonRectangle_mem_hexagonRectangleDecompositions {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridInitialPentagonBetween C.column C.oppositeTurnRow y z)
    (hcol : Q.right ∈ Grid.cIoo (finRotate n C.column) P.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty)
    (hPX : Disjoint P.coveredSquares G.XSet)
    (hQX : Disjoint Q.coveredSquares
      (G.swapColumns C.column (finRotate n C.column)).XSet) :
    P.recutHexagonRectangle Q hcol hP hQ ∈ G.hexagonRectangleDecompositions C x z := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.second.right ∈ Grid.cIoo D.first.left D.first.right := P.left_eq ▸ hcol
  let hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hc
  let F := P.recutHexagonRectangle Q hcol hP hQ
  have hF : F.toRectangleDecomposition = D.recut hone hP hQ :=
    P.recutHexagonRectangle_toRectangleDecomposition Q hcol hP hQ
  have hrecut : D.IsRecut F.toRectangleDecomposition :=
    hF.symm ▸ D.isRecut_recut hone hP hQ
  have hsides := D.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hc hP hQ
  rw [← hF] at hsides
  have hsecondLeft : F.rectangle.left = Q.right := hsides.2.2.1
  have hsecondRight : F.rectangle.right = P.right := hsides.2.2.2
  -- The rectangle repartition transports square coverage; marking avoidance is read
  -- in the original diagram away from the two commuted columns.
  have hcov {p : Fin n × Fin n}
      (hp : p ∈ F.hexagon.toGridRectangleBetween.toGridRectangle.coveredSquares ∪
        F.rectangle.toGridRectangle.coveredSquares) :
      p ∈ P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares := by
    exact hrecut.isRepartition.coveredSquares_union_eq ▸ hp
  rw [G.mem_hexagonRectangleDecompositions C, G.mem_commutationHexagons C,
    G.mem_unblockedRectangles]
  refine ⟨⟨hrecut.isEmpty_first, ?_⟩, hrecut.isEmpty_second, ?_⟩
  · cases hhex : F.hexagon with
    | inl H =>
      have hside := P.recutHexagonRectangle_hexagon_isLeft Q hcol hP hQ
      simp only [F, hhex, Sum.isLeft_inl, Bool.true_eq_false] at hside
    | inr H =>
      rw [GridCommutationHexagonBetween.coveredSquares_inr, Finset.disjoint_right]
      intro p hpX hp
      obtain ⟨hb, hp⟩ := (H.mem_coveredSquares p).mp hp
      have ha : p.1 ≠ C.column := by
        intro heq
        have hcolumn := ((H.toGridRectangle.mem_coveredSquares p).mp hp).1
        simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
          GridRectangleBetween.toGridRectangle_right, H.left_eq, heq] at hcolumn
        simp at hcolumn
      apply G.initialPair_notMem_XSet_away C P Q hPX hQX ha hb _ hpX
      apply hcov
      apply Finset.mem_union_left
      simpa only [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inr] using hp
  -- The remaining rectangle lies strictly between the two terminal sides, so it
  -- meets neither commuted column.
  · rw [Finset.disjoint_right]
    intro p hpX hp
    have hcolumn := ((F.rectangle.toGridRectangle.mem_coveredSquares p).mp hp).1
    simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hsecondLeft, hsecondRight] at hcolumn
    have hbig := Grid.cIco_subset_of_mem_cIoo hcol hcolumn
    have ha : p.1 ≠ C.column := by
      intro heq
      simp only [heq] at hbig
      simp at hbig
    have hb : p.1 ≠ finRotate n C.column := by
      intro heq
      exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)
        (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol).symm) (heq ▸ hcolumn)
    exact G.initialPair_notMem_XSet_away C P Q hPX hQX ha hb
      (hcov (Finset.mem_union_right _ hp)) hpX

/-- The complementary initial-side pentagon recut is a counted rectangle--hexagon composite
when the forward and reverse pentagons avoid their respective `X`-markings. -/
theorem recutRectangleHexagon_mem_rectangleHexagonDecompositions {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridInitialPentagonBetween C.column C.oppositeTurnRow y z)
    (hcol : P.right ∈ Grid.cIoo (finRotate n C.column) Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty)
    (hPX : Disjoint P.coveredSquares G.XSet)
    (hQX : Disjoint Q.coveredSquares
      (G.swapColumns C.column (finRotate n C.column)).XSet) :
    P.recutRectangleHexagon Q hcol hP hQ ∈ G.rectangleHexagonDecompositions C x z := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.first.right ∈ Grid.cIoo D.first.left D.second.right := P.left_eq ▸ hcol
  let hone := D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hc)
  let F := P.recutRectangleHexagon Q hcol hP hQ
  have hF : F.toRectangleDecomposition = D.recut hone hP hQ :=
    P.recutRectangleHexagon_toRectangleDecomposition Q hcol hP hQ
  have hrecut : D.IsRecut F.toRectangleDecomposition :=
    hF.symm ▸ D.isRecut_recut hone hP hQ
  have hsides := D.recut_sides_of_left_eq_left_of_first_right_mem_cIoo
    hcommon hc hP hQ
  rw [← hF] at hsides
  have hfirstLeft : F.rectangle.left = P.right := hsides.1
  have hfirstRight : F.rectangle.right = Q.right := hsides.2.1
  have hcov {p : Fin n × Fin n}
      (hp : p ∈ F.rectangle.toGridRectangle.coveredSquares ∪
        F.hexagon.toGridRectangleBetween.toGridRectangle.coveredSquares) :
      p ∈ P.toGridRectangle.coveredSquares ∪ Q.toGridRectangle.coveredSquares := by
    exact hrecut.isRepartition.coveredSquares_union_eq ▸ hp
  rw [G.mem_rectangleHexagonDecompositions C, G.mem_unblockedRectangles,
    G.mem_commutationHexagons C]
  refine ⟨⟨hrecut.isEmpty_first, ?_⟩, ⟨hrecut.isEmpty_second, ?_⟩⟩
  · rw [Finset.disjoint_right]
    intro p hpX hp
    have hcolumn := ((F.rectangle.toGridRectangle.mem_coveredSquares p).mp hp).1
    simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hfirstLeft, hfirstRight] at hcolumn
    have hbig := Grid.cIco_subset_of_mem_cIoo hcol hcolumn
    have ha : p.1 ≠ C.column := by
      intro heq
      simp only [heq] at hbig
      simp at hbig
    have hb : p.1 ≠ finRotate n C.column := by
      intro heq
      exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)
        (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol).symm) (heq ▸ hcolumn)
    exact G.initialPair_notMem_XSet_away C P Q hPX hQX ha hb
      (hcov (Finset.mem_union_left _ hp)) hpX
  · cases hhex : F.hexagon with
    | inl H =>
      have hside := P.recutRectangleHexagon_hexagon_isLeft Q hcol hP hQ
      simp only [F, hhex, Sum.isLeft_inl, Bool.true_eq_false] at hside
    | inr H =>
      rw [GridCommutationHexagonBetween.coveredSquares_inr, Finset.disjoint_right]
      intro p hpX hp
      obtain ⟨hb, hp⟩ := (H.mem_coveredSquares p).mp hp
      have ha : p.1 ≠ C.column := by
        intro heq
        have hcolumn := ((H.toGridRectangle.mem_coveredSquares p).mp hp).1
        simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
          GridRectangleBetween.toGridRectangle_right, H.left_eq, heq] at hcolumn
        simp at hcolumn
      apply G.initialPair_notMem_XSet_away C P Q hPX hQX ha hb _ hpX
      apply hcov
      apply Finset.mem_union_right
      simpa only [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inr] using hp

private theorem initialPair_ne_composite {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridInitialPentagonBetween C.column C.oppositeTurnRow y z)
    (hright : P.right ≠ Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty)
    (E : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    E.toRectangleDecomposition ≠
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) := by
  have hturns := (P.pair_turn_order Q hright hP hQ).2
  intro h
  cases E with
  | inl E =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at h
    have hgeom : E.hexagon.toGridRectangleBetween.toGridRectangle = P.toGridRectangle :=
      congrArg (fun F : GridRectangleDecomposition x z => F.first.toGridRectangle) h
    cases hhex : E.hexagon with
    | inl H =>
      rw [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hgeom
      have hl := congrArg GridRectangle.left hgeom
      exact H.left_ne (hl.trans P.left_eq)
    | inr H =>
      rw [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hgeom
      have htop : H.top = P.top := by
        simpa only [GridRectangleBetween.toGridRectangle_top] using
          congrArg GridRectangle.top hgeom
      have ht := H.upper_mem
      rw [← H.top_def, htop] at ht
      exact hturns.1 ht
  | inr E =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at h
    have hgeom : E.hexagon.toGridRectangleBetween.toGridRectangle = Q.toGridRectangle :=
      congrArg (fun F : GridRectangleDecomposition x z => F.second.toGridRectangle) h
    cases hhex : E.hexagon with
    | inl H =>
      rw [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inl] at hgeom
      have hl := congrArg GridRectangle.left hgeom
      exact H.left_ne (hl.trans Q.left_eq)
    | inr H =>
      rw [hhex, GridCommutationHexagonBetween.toGridRectangleBetween_inr] at hgeom
      have hb : H.bottom = Q.bottom := by
        simpa only [GridRectangleBetween.toGridRectangle_bottom] using
          congrArg GridRectangle.bottom hgeom
      have ht : H.top = Q.top := by
        simpa only [GridRectangleBetween.toGridRectangle_top] using
          congrArg GridRectangle.top hgeom
      have hs := H.lower_mem
      rw [← H.bottom_def, ← H.top_def, hb, ht] at hs
      exact hturns.2 hs

/-- The counted initial-side pentagon recut has no counted composite recut partner.
The original pentagon pair cannot contain a hexagon: neither of its row intervals
contains both turn rows in the required order. -/
theorem recutHexagonRectangle_mem_unpairedHexagonComposites {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridInitialPentagonBetween C.column C.oppositeTurnRow y z)
    (hcol : Q.right ∈ Grid.cIoo (finRotate n C.column) P.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty)
    (hPX : Disjoint P.coveredSquares G.XSet)
    (hQX : Disjoint Q.coveredSquares
      (G.swapColumns C.column (finRotate n C.column)).XSet) :
    Sum.inl (P.recutHexagonRectangle Q hcol hP hQ) ∈
      G.unpairedHexagonComposites C x z := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.second.right ∈ Grid.cIoo D.first.left D.first.right := P.left_eq ▸ hcol
  let hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hc
  let F := P.recutHexagonRectangle Q hcol hP hQ
  have hF : F.toRectangleDecomposition = D.recut hone hP hQ :=
    P.recutHexagonRectangle_toRectangleDecomposition Q hcol hP hQ
  have hrecut : D.IsRecut F.toRectangleDecomposition :=
    hF.symm ▸ D.isRecut_recut hone hP hQ
  have hsymm := hrecut.symm hone hP hQ
  have honeF := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hsymm
    (D.target_ne_source_of_hasOneCommonSide hone)
  rw [G.mem_unpairedHexagonComposites C,
    G.inl_mem_hexagonCompositeDecompositions C,
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
  refine ⟨G.recutHexagonRectangle_mem_hexagonRectangleDecompositions C P Q hcol hP hQ hPX hQX,
    F.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide honeF, ?_⟩
  intro E _ hE
  have heq : E.toRectangleDecomposition = D :=
    (F.toRectangleDecomposition.existsUnique_isRecut honeF
      hrecut.isEmpty_first hrecut.isEmpty_second).unique hE (hrecut.symm hone hP hQ)
  exact G.initialPair_ne_composite C P Q (Grid.ne_right_of_mem_cIoo hcol).symm hP hQ E heq

/-- The counted complementary initial-side recut has no counted composite recut partner. -/
theorem recutRectangleHexagon_mem_unpairedHexagonComposites {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridInitialPentagonBetween C.column C.oppositeTurnRow y z)
    (hcol : P.right ∈ Grid.cIoo (finRotate n C.column) Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty)
    (hPX : Disjoint P.coveredSquares G.XSet)
    (hQX : Disjoint Q.coveredSquares
      (G.swapColumns C.column (finRotate n C.column)).XSet) :
    Sum.inr (P.recutRectangleHexagon Q hcol hP hQ) ∈
      G.unpairedHexagonComposites C x z := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hcommon : D.first.left = D.second.left := P.left_eq.trans Q.left_eq.symm
  have hc : D.first.right ∈ Grid.cIoo D.first.left D.second.right := P.left_eq ▸ hcol
  let hone := D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hc)
  let F := P.recutRectangleHexagon Q hcol hP hQ
  have hF : F.toRectangleDecomposition = D.recut hone hP hQ :=
    P.recutRectangleHexagon_toRectangleDecomposition Q hcol hP hQ
  have hrecut : D.IsRecut F.toRectangleDecomposition :=
    hF.symm ▸ D.isRecut_recut hone hP hQ
  have hsymm := hrecut.symm hone hP hQ
  have honeF := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hsymm
    (D.target_ne_source_of_hasOneCommonSide hone)
  rw [G.mem_unpairedHexagonComposites C,
    G.inr_mem_hexagonCompositeDecompositions C,
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
  refine ⟨G.recutRectangleHexagon_mem_rectangleHexagonDecompositions
      C P Q hcol hP hQ hPX hQX,
    F.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide honeF, ?_⟩
  intro E _ hE
  have heq : E.toRectangleDecomposition = D :=
    (F.toRectangleDecomposition.existsUnique_isRecut honeF
      hrecut.isEmpty_first hrecut.isEmpty_second).unique hE (hrecut.symm hone hP hQ)
  exact G.initialPair_ne_composite C P Q (Grid.ne_right_of_mem_cIoo hcol) hP hQ E heq

/-- Two counted initial-side pentagons for an actual commutation and its reverse admit
an unpaired hexagon-composite recut in the strict interior-terminal-side branch.
The reverse pentagon retains the indices of `C.reverse`. -/
theorem exists_unpairedHexagonComposite_of_initialPentagonPair {x y z : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns C.column (finRotate n C.column)).initialPentagons C.reverse y z)
    (hcol : Q.right ∈ Grid.cIoo (finRotate n C.column) P.right) :
    ∃ F ∈ G.unpairedHexagonComposites C x z,
      GridRectangleDecomposition.IsRecut
        (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
          GridRectangleDecomposition x z) F.toRectangleDecomposition := by
  -- Generalize the reverse data before identifying its indices; this retains its
  -- marking proofs without rewriting dependent polygon projections.
  generalize hCr : C.reverse = Cr at *
  have hcolumn : Cr.column = C.column := hCr ▸ C.reverse_column
  have hturn : Cr.turnRow = C.oppositeTurnRow := hCr ▸ C.reverse_turnRow
  rcases Cr with ⟨⟨column, turn, hne⟩, opposite, hnon, hOa, hXa, hOb, hXb⟩
  simp only at hcolumn hturn
  subst column turn
  obtain ⟨hPE, hPX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hQE, hQX⟩ := ((G.swapColumns C.column
    (finRotate n C.column)).mem_initialPentagons Q).mp hQ
  refine ⟨Sum.inl (P.recutHexagonRectangle Q hcol hPE hQE),
    G.recutHexagonRectangle_mem_unpairedHexagonComposites C P Q hcol hPE hQE hPX hQX, ?_⟩
  rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
  exact P.isRecut_recutHexagonRectangle Q hcol hPE hQE

end GridDiagram
end TauCeti
