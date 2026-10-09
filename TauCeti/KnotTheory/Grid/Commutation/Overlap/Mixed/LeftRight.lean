/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Weight

/-!
# Recutting a rectangle that starts on the replaced line before a pentagon

Consider a rectangle of the original diagram followed by a commutation pentagon turning on its
terminal side. This file treats the mixed overlap in which the rectangle's initial side is the
pentagon's terminal side, which is the grid line `b = finRotate n a` replaced in the commutation.
If the rectangle does not contain the turn row, the generic empty-rectangle recut has its first
rectangle ending on `b` and containing the turn row. It therefore promotes to a pentagon followed
by a rectangle of the commuted diagram.

The excluded case, where the rectangle contains the turn row, is the turn-point cut
`GridDiagram.rectanglePentagonTurnCuts`: the same two underlying rectangles are instead read as an
initial-side pentagon followed by a rectangle. This file is the half-turn mirror of the mixed
`right = left` overlap of initial-side pentagons in
`TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.RightLeft`.

Write `f` for the rectangle's terminal side and `c` for the pentagon's initial side, and `p`, `q`,
`r` for the rows of the source state on `b`, `c` and `f`. The two domains share their top row `r`.
Emptiness and the position of the turn row force `p` strictly between `q` and `r`, so the turn row
lies between `q` and `p`. The recut consists of the pentagon from `c` to `b` over the rows from `q`
to `p`, followed by the rectangle from `c` to `f` over the rows from `p` to `r`
(`GridRectanglePentagonDecomposition.recutLeftEqRight_geometry`). The new rectangle covers both
columns next to `b` in the same rows, so exchanging these two columns does not change its squares,
and the two pentagons have the same bottom row. Hence both composite domains cover the same squares
with the same multiplicities (`coveredSquares_val_add_val_recutLeftEqRight`), the recut of a
counted domain is counted with the same monomial weight, and these terms cancel between the
rectangle--pentagon and pentagon--rectangle sums of the chain-map equation
(`GridDiagram.add_sum_rectanglePentagonWeight_eq_add_sum_iff_sdiff_leftRightOverlap`).

## Main definitions

* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqRight`: the promoted
  pentagon--rectangle recut of the mixed `left = right` overlap.
* `TauCeti.GridDiagram.leftRightOverlapSources`: the counted rectangle--pentagon domains with this
  mixed overlap, outside the turn-point cut.
* `TauCeti.GridDiagram.leftRightOverlapPartners`: their recuts.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.isRecut_recutLeftEqRight`: the promoted
  decomposition is an empty-rectangle recut of the original domain.
* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqRight_geometry`: its sides and rows; its
  pentagon and rectangle share their initial side.
* `TauCeti.GridRectanglePentagonDecomposition.coveredSquares_val_add_val_recutLeftEqRight`: both
  decompositions cover the same squares with the same multiplicities.
* `TauCeti.GridDiagram.recutLeftEqRight_mem_pentagonRectangleDecompositions` and
  `TauCeti.GridDiagram.pentagonRectangleWeight_recutLeftEqRight`: the recut of a counted domain is
  counted, with the same weight.
* `TauCeti.GridDiagram.sum_rectanglePentagonWeight_leftRightOverlapSources_eq_sum_partners` and
  `TauCeti.GridDiagram.add_sum_rectanglePentagonWeight_eq_add_sum_iff_sdiff_leftRightOverlap`:
  the sources and their recuts contribute equally and can be removed from the chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The underlying rectangles of a rectangle--pentagon decomposition have the rows of the
rectangle and of the pentagon. -/
private theorem toRectangleDecomposition_rows (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.first.bottom = D.rectangle.bottom ∧
      D.toRectangleDecomposition.first.top = D.rectangle.top ∧
        D.toRectangleDecomposition.second.bottom = D.pentagon.bottom := by
  have hfirst := D.toRectangleDecomposition_first_toGridRectangle
  have hsecond := D.toRectangleDecomposition_second_toGridRectangle
  exact ⟨by simpa only [GridRectangleBetween.toGridRectangle_bottom] using
      congrArg GridRectangle.bottom hfirst,
    by simpa only [GridRectangleBetween.toGridRectangle_top] using
      congrArg GridRectangle.top hfirst,
    by simpa only [GridRectangleBetween.toGridRectangle_bottom] using
      congrArg GridRectangle.bottom hsecond⟩

/-- In a mixed overlap whose rectangle starts where the pentagon ends, the two domains share their
top row. -/
private theorem pentagon_top_eq_rectangle_top (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right) :
    D.pentagon.top = D.rectangle.top := by
  rw [GridRectangleBetween.top_def, ← hcommon, D.rectangle.map_left,
    GridRectangleBetween.top_def]

/-- If the rectangle avoids the turn row, the noncommon sides of a mixed `left = right` overlap
differ: otherwise the pentagon would span the rectangle's rows and contain the turn row. -/
theorem rectangle_right_ne_pentagon_left_of_left_eq_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    D.rectangle.right ≠ D.pentagon.left := by
  intro hother
  have hbottom : D.pentagon.bottom = D.rectangle.bottom := by
    rw [GridRectangleBetween.bottom_def, ← hother, D.rectangle.map_right,
      GridRectangleBetween.bottom_def]
  exact hturn (by
    simpa only [hbottom, D.pentagon_top_eq_rectangle_top hcommon] using
      D.pentagon.turn_mem_cIco_bottom_top)

/-- A mixed overlap whose rectangle initial side is the pentagon terminal side has exactly one
common side column when its two other sides differ. -/
theorem hasOneCommonSide_of_left_eq_right (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hother : D.rectangle.right ≠ D.pentagon.left) :
    D.toRectangleDecomposition.HasOneCommonSide := by
  apply D.toRectangleDecomposition.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.rectangle.left, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left,
      toRectangleDecomposition_second_right] at hc
    have hfirst := D.rectangle.left_ne_right
    have hsecond := D.pentagon.left_ne_right
    grind

/-- The generic recut of a mixed `left = right` overlap whose rectangle avoids the turn row. -/
private noncomputable def leftRightRecut (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    GridRectangleDecomposition x z :=
  D.recutOfIsEmpty (D.hasOneCommonSide_of_left_eq_right hcommon
      (D.rectangle_right_ne_pentagon_left_of_left_eq_right hcommon hturn))
    hrectangle hpentagon

private theorem leftRightRecut_geometry (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    let E := D.leftRightRecut hcommon hrectangle hpentagon hturn
    E.middle = x.swapRows D.pentagon.bottom D.rectangle.bottom ∧
      E.first.bottom = D.pentagon.bottom ∧ E.first.top = D.rectangle.bottom ∧
        E.second.bottom = D.rectangle.bottom ∧ E.second.top = D.rectangle.top ∧
          D.rectangle.bottom ∈ Grid.cIoo D.pentagon.bottom D.rectangle.top := by
  intro E
  have hone := D.hasOneCommonSide_of_left_eq_right hcommon
    (D.rectangle_right_ne_pentagon_left_of_left_eq_right hcommon hturn)
  obtain ⟨hfb, hft, hsb⟩ := D.toRectangleDecomposition_rows
  have hdata : D.toRectangleDecomposition.IsRecutOfLeftEqRight E := by
    simp only [E, leftRightRecut]
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.toRectangleDecomposition.isRecutOfLeftEqRight_recut
      (by simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_right]
        using hcommon) hone _ _
  obtain ⟨hEfb, hEsb⟩ := hdata.recut_sides
  rcases hdata.recut_branch with ⟨hrow, hmiddle, hEft, hEst⟩ | ⟨hrow, -⟩
  · simp only [hfb, hft, hsb] at hEfb hEsb hrow hmiddle hEft hEst
    exact ⟨hmiddle, hEfb, hEft, hEsb, hEst, hrow⟩
  · -- In the other branch the pentagon's rows lie inside the rectangle's, and so does the turn row.
    simp only [hfb, hft, hsb] at hrow
    refine (hturn (Grid.cIco_subset_of_mem_cIoo hrow ?_)).elim
    simpa only [D.pentagon_top_eq_rectangle_top hcommon] using
      D.pentagon.turn_mem_cIco_bottom_top

private theorem leftRightRecut_first_right (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    (D.leftRightRecut hcommon hrectangle hpentagon hturn).first.right = finRotate n a := by
  obtain ⟨-, -, htop, -⟩ := D.leftRightRecut_geometry hcommon hrectangle hpentagon hturn
  rw [← D.pentagon.right_eq, ← hcommon]
  apply x.toPerm.injective
  exact ((GridRectangleBetween.top_def _).symm.trans htop).trans
    (GridRectangleBetween.bottom_def _)

private theorem leftRightRecut_first_turn_mem (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    s ∈ Grid.cIco (D.leftRightRecut hcommon hrectangle hpentagon hturn).first.bottom
      (D.leftRightRecut hcommon hrectangle hpentagon hturn).first.top := by
  obtain ⟨-, hbottom, htop, -, -, hrow⟩ :=
    D.leftRightRecut_geometry hcommon hrectangle hpentagon hturn
  have hturnWhole : s ∈ Grid.cIco D.pentagon.bottom D.rectangle.bottom ∪
      Grid.cIco D.rectangle.bottom D.rectangle.top := by
    rw [Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow,
      ← D.pentagon_top_eq_rectangle_top hcommon]
    exact D.pentagon.turn_mem_cIco_bottom_top
  rw [hbottom, htop]
  exact (Finset.mem_union.mp hturnWhole).resolve_right hturn

/-- Promote the first generic recut rectangle to a pentagon. This is the recut of a mixed
`left = right` overlap outside the turn-point-cut family. -/
noncomputable def recutLeftEqRight (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    GridPentagonRectangleDecomposition a s x z where
  middle := (D.leftRightRecut hcommon hrectangle hpentagon hturn).middle
  first := GridPentagonBetween.ofRightEq
    (D.leftRightRecut hcommon hrectangle hpentagon hturn).first
    (D.leftRightRecut_first_right hcommon hrectangle hpentagon hturn)
    (D.leftRightRecut_first_turn_mem hcommon hrectangle hpentagon hturn)
  second := (D.leftRightRecut hcommon hrectangle hpentagon hturn).second

/-- Forgetting the turn row of the promoted decomposition recovers the generic recut. -/
@[simp]
theorem recutLeftEqRight_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    (D.recutLeftEqRight hcommon hrectangle hpentagon hturn).toRectangleDecomposition =
      D.recutOfIsEmpty (D.hasOneCommonSide_of_left_eq_right hcommon
          (D.rectangle_right_ne_pentagon_left_of_left_eq_right hcommon hturn))
        hrectangle hpentagon := by
  apply GridRectangleDecomposition.ext
  · simp only [recutLeftEqRight,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left]
    exact GridPentagonBetween.ofRightEq_left _ _ _
  · simp only [recutLeftEqRight,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
      GridPentagonRectangleDecomposition.pentagon, GridPentagonBetween.ofRightEq_right]
    exact (D.leftRightRecut_first_right hcommon hrectangle hpentagon hturn).symm
  · simp only [recutLeftEqRight,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left, leftRightRecut]
  · simp only [recutLeftEqRight,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right, leftRightRecut]

/-- The promoted decomposition is an empty-rectangle recut of the original composite domain. -/
theorem isRecut_recutLeftEqRight (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    D.toRectangleDecomposition.IsRecut
      (D.recutLeftEqRight hcommon hrectangle hpentagon hturn).toRectangleDecomposition := by
  rw [recutLeftEqRight_toRectangleDecomposition]
  exact D.isRecut_recutOfIsEmpty _ _ _

/-- The promoted recut of a mixed `left = right` overlap passes through the source state with its
rows on the original pentagon's and the original rectangle's initial sides swapped. Its pentagon
spans the rows from the original pentagon's bottom to the original rectangle's bottom, and its
rectangle spans the rows of the original rectangle. Both start on the original pentagon's initial
side. -/
theorem recutLeftEqRight_geometry (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    let E := D.recutLeftEqRight hcommon hrectangle hpentagon hturn
    E.middle = x.swapRows D.pentagon.bottom D.rectangle.bottom ∧
      E.pentagon.left = D.pentagon.left ∧ E.rectangle.left = D.pentagon.left ∧
        E.pentagon.bottom = D.pentagon.bottom ∧ E.pentagon.top = D.rectangle.bottom ∧
          E.rectangle.bottom = D.rectangle.bottom ∧ E.rectangle.top = D.rectangle.top := by
  intro E
  obtain ⟨hmiddle, hbottom, htop, hsecondBottom, hsecondTop, -⟩ :=
    D.leftRightRecut_geometry hcommon hrectangle hpentagon hturn
  have hEbottom : E.pentagon.bottom = D.pentagon.bottom := by
    simpa only [E, recutLeftEqRight, GridPentagonRectangleDecomposition.pentagon,
      GridPentagonBetween.ofRightEq_bottom] using hbottom
  have hEtop : E.pentagon.top = D.rectangle.bottom := by
    simpa only [E, recutLeftEqRight, GridPentagonRectangleDecomposition.pentagon,
      GridPentagonBetween.ofRightEq_top] using htop
  have hErbottom : E.rectangle.bottom = D.rectangle.bottom := by
    simpa only [E, recutLeftEqRight, GridPentagonRectangleDecomposition.rectangle] using
      hsecondBottom
  -- The source state has the same row on the pentagon's initial side before and after the
  -- rectangle, since that side is not a side of the rectangle.
  have hpentagonLeft : E.pentagon.left = D.pentagon.left := by
    apply x.toPerm.injective
    have hleft : D.pentagon.left ≠ D.rectangle.left := hcommon ▸ D.pentagon.left_ne_right
    have hright : D.pentagon.left ≠ D.rectangle.right :=
      (D.rectangle_right_ne_pentagon_left_of_left_eq_right hcommon hturn).symm
    exact ((GridRectangleBetween.bottom_def _).symm.trans hEbottom).trans
      ((GridRectangleBetween.bottom_def _).trans (D.rectangle.map_of_ne _ hleft hright))
  -- The intermediate state has the row of the rectangle's bottom on the pentagon's initial side
  -- and on the rectangle's initial side.
  have hrectangleLeft : E.rectangle.left = E.pentagon.left := by
    apply E.middle.toPerm.injective
    exact ((GridRectangleBetween.bottom_def _).symm.trans hErbottom).trans
      (((GridRectangleBetween.bottom_def _).trans
        (by rw [hcommon, D.pentagon.right_eq, E.pentagon.right_eq])).trans
        E.pentagon.map_left.symm)
  exact ⟨by simpa only [E, recutLeftEqRight] using hmiddle, hpentagonLeft,
    hrectangleLeft.trans hpentagonLeft, hEbottom, hEtop, hErbottom,
    by simpa only [E, recutLeftEqRight] using hsecondTop⟩

/-- The promoted recut of a mixed `left = right` overlap covers the squares of the original domain
with the same multiplicities, the rectangle of the commuted diagram being read in the original
diagram with the two columns next to the replaced line exchanged. -/
theorem coveredSquares_val_add_val_recutLeftEqRight
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    (D.recutLeftEqRight hcommon hrectangle hpentagon hturn).pentagon.coveredSquares.val +
        ((D.recutLeftEqRight hcommon hrectangle hpentagon
            hturn).rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  obtain ⟨-, hEleft, -, hEbottom, hEtop, -, -⟩ :=
    D.recutLeftEqRight_geometry hcommon hrectangle hpentagon hturn
  obtain ⟨-, -, -, -, -, hrow⟩ := D.leftRightRecut_geometry hcommon hrectangle hpentagon hturn
  have hrep := (D.isRecut_recutLeftEqRight hcommon hrectangle hpentagon hturn).isRepartition
  set E := D.recutLeftEqRight hcommon hrectangle hpentagon hturn
  have htop := D.pentagon_top_eq_rectangle_top hcommon
  have hb : D.rectangle.left = finRotate n a := hcommon.trans D.pentagon.right_eq
  -- Both pentagons end on the replaced line and the original rectangle starts there, so the
  -- pentagons cover the column before that line but not the column after it, while the original
  -- rectangle covers the column after it but not the column before it.
  have haD1 : a ∉ Grid.cIco D.rectangle.left D.rectangle.right := by
    rw [hb]
    simp
  have hbD1 : finRotate n a ∈ Grid.cIco D.rectangle.left D.rectangle.right := by
    rw [← hb]
    exact Grid.left_mem_cIco D.rectangle.left_ne_right
  have haP : a ∈ Grid.cIco D.pentagon.left (finRotate n a) :=
    Grid.self_mem_cIco_finRotate D.pentagon.left_ne
  have hbP : finRotate n a ∉ Grid.cIco D.pentagon.left (finRotate n a) :=
    Grid.right_notMem_cIco _ _
  -- The original pentagon's rows are those of the new pentagon followed by those of the
  -- rectangle.
  have hsplit (t : Fin n) :
      (if t ∈ Grid.cIco D.pentagon.bottom D.rectangle.top then 1 else 0 : ℕ) =
        (if t ∈ Grid.cIco D.pentagon.bottom D.rectangle.bottom then 1 else 0) +
          if t ∈ Grid.cIco D.rectangle.bottom D.rectangle.top then 1 else 0 := by
    have hrow' := hrow
    simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hrow' ⊢
    split_ifs at hrow' ⊢ <;> omega
  have hcounts := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle] at hcounts
  refine D.coveredSquares_val_add_val_eq_of_isRepartition E hrep fun t => ?_
  -- In the column after the replaced line, the new rectangle covers the rows of the original
  -- rectangle.
  have hb' := hcounts (finRotate n a, t)
  -- In the column before it, the new rectangle covers the rows of the original pentagon that the
  -- new pentagon does not.
  have ha' := hcounts (a, t)
  simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
    ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def] at ha' hb' ⊢
  simp only [D.pentagon.right_eq, E.pentagon.right_eq, hEleft, hEbottom, hEtop, htop, haD1,
    hbD1, haP, hbP, true_and, false_and, ↓reduceIte] at ha' hb' ⊢
  have := hsplit t
  omega

end TauCeti.GridRectanglePentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

section Weights

variable (R : Type*) [CommSemiring R]

variable {x z : GridState n}
  (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.rectangle.left = D.pentagon.right)
  (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∉ Grid.cIco D.rectangle.bottom D.rectangle.top)

/-- Recutting a mixed `left = right` overlap outside the turn-point cut preserves the weight. -/
@[simp]
theorem pentagonRectangleWeight_recutLeftEqRight :
    G.pentagonRectangleWeight C R (D.recutLeftEqRight hcommon hrectangle hpentagon hturn) =
      G.rectanglePentagonWeight C R D :=
  G.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutLeftEqRight hcommon hrectangle hpentagon hturn)

end Weights

variable {x z : GridState n}
  (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.rectangle.left = D.pentagon.right)
  (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∉ Grid.cIco D.rectangle.bottom D.rectangle.top)

/-- The recut of a counted mixed `left = right` overlap outside the turn-point cut is a counted
pentagon--rectangle domain. -/
theorem recutLeftEqRight_mem_pentagonRectangleDecompositions
    (hD : D ∈ G.rectanglePentagonDecompositions C x z) :
    D.recutLeftEqRight hcommon hrectangle hpentagon hturn ∈
      G.pentagonRectangleDecompositions C x z :=
  have hrecut := D.isRecut_recutLeftEqRight hcommon hrectangle hpentagon hturn
  G.mem_pentagonRectangleDecompositions_of_val_add_val_eq C hD
    (GridPentagonRectangleDecomposition.isEmpty_pentagon_of_isRecut _ hrecut)
    (GridPentagonRectangleDecomposition.isEmpty_rectangle_of_isRecut _ hrecut)
    (D.coveredSquares_val_add_val_recutLeftEqRight hcommon hrectangle hpentagon hturn)

/-! ### Cancelling the mixed `left = right` terms -/

variable (x z) in
/-- The counted rectangle--pentagon decompositions whose rectangle starts where the pentagon ends
and does not span the turn row: the mixed `left = right` overlaps outside the turn-point cut. -/
noncomputable def leftRightOverlapSources :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectanglePentagonDecompositions C x z).filter fun D =>
    D.rectangle.left = D.pentagon.right ∧ C.turnRow ∉ Grid.cIco D.rectangle.bottom D.rectangle.top

/-- Membership in the mixed `left = right` source family records counting, the common side and
that the rectangle avoids the turn row. -/
@[simp]
theorem mem_leftRightOverlapSources :
    D ∈ G.leftRightOverlapSources C x z ↔
      D ∈ G.rectanglePentagonDecompositions C x z ∧
        D.rectangle.left = D.pentagon.right ∧
          C.turnRow ∉ Grid.cIco D.rectangle.bottom D.rectangle.top := by
  classical
  simp [leftRightOverlapSources]

private theorem leftRightOverlapSource_data (hD : D ∈ G.leftRightOverlapSources C x z) :
    D.rectangle.left = D.pentagon.right ∧
      C.turnRow ∉ Grid.cIco D.rectangle.bottom D.rectangle.top ∧
        D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty := by
  obtain ⟨hcounted, hcommon, hturn⟩ := (G.mem_leftRightOverlapSources C D).1 hD
  rw [G.mem_rectanglePentagonDecompositions, G.mem_unblockedRectangles, G.mem_pentagons]
    at hcounted
  exact ⟨hcommon, hturn, hcounted.1.1, hcounted.2.1⟩

private noncomputable def leftRightOverlapPartner
    (D : {D // D ∈ G.leftRightOverlapSources C x z}) :
    GridPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutLeftEqRight
    (G.leftRightOverlapSource_data C D.val D.property).1
    (G.leftRightOverlapSource_data C D.val D.property).2.2.1
    (G.leftRightOverlapSource_data C D.val D.property).2.2.2
    (G.leftRightOverlapSource_data C D.val D.property).2.1

private theorem leftRightOverlapPartner_isRecut
    (D : {D // D ∈ G.leftRightOverlapSources C x z}) :
    D.val.toRectangleDecomposition.IsRecut
      (G.leftRightOverlapPartner C D).toRectangleDecomposition :=
  D.val.isRecut_recutLeftEqRight _ _ _ _

/-- A source has exactly one common side and two empty underlying rectangles, so it has a unique
recut. -/
private theorem leftRightOverlapSource_recut_data (hD : D ∈ G.leftRightOverlapSources C x z) :
    D.toRectangleDecomposition.HasOneCommonSide ∧ D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨hcommon, hturn, hrectangle, hpentagon⟩ := G.leftRightOverlapSource_data C D hD
  refine ⟨D.hasOneCommonSide_of_left_eq_right hcommon
    (D.rectangle_right_ne_pentagon_left_of_left_eq_right hcommon hturn), ?_, ?_⟩
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
      using hpentagon

private theorem leftRightOverlapPartner_injective :
    Function.Injective (G.leftRightOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.leftRightOverlapPartner_isRecut C D
  have hE := G.leftRightOverlapPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨honeD, hfD, hsD⟩ := G.leftRightOverlapSource_recut_data C D.val D.property
  obtain ⟨honeE, hfE, hsE⟩ := G.leftRightOverlapSource_recut_data C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

variable (x z) in
/-- The pentagon--rectangle partners obtained by recutting the mixed `left = right` sources: the
exact recut image of `GridDiagram.leftRightOverlapSources`. -/
noncomputable def leftRightOverlapPartners :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.leftRightOverlapSources C x z).attach.map
    ⟨G.leftRightOverlapPartner C, G.leftRightOverlapPartner_injective C⟩

/-- A pentagon--rectangle term is a partner exactly when its underlying rectangles are the recut
of a mixed `left = right` source. -/
@[simp]
theorem mem_leftRightOverlapPartners
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.leftRightOverlapPartners C x z ↔
      ∃ D ∈ G.leftRightOverlapSources C x z,
        D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
  classical
  simp only [leftRightOverlapPartners, Finset.mem_map, Finset.mem_attach, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.leftRightOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨hone, hf, hs⟩ := G.leftRightOverlapSource_recut_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
    exact (D.toRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
      (G.leftRightOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Each mixed `left = right` source belongs to the rectangle--pentagon sum. -/
theorem leftRightOverlapSources_subset :
    G.leftRightOverlapSources C x z ⊆ G.rectanglePentagonDecompositions C x z := fun D hD =>
  ((G.mem_leftRightOverlapSources C D).1 hD).1

/-- Each partner belongs to the pentagon--rectangle sum. -/
theorem leftRightOverlapPartners_subset :
    G.leftRightOverlapPartners C x z ⊆ G.pentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [leftRightOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  exact G.recutLeftEqRight_mem_pentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_leftRightOverlapSources C D.val).1 D.property).1

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- Recutting identifies the total contribution of the mixed `left = right` sources with the total
contribution of their partners. -/
theorem sum_rectanglePentagonWeight_leftRightOverlapSources_eq_sum_partners :
    ∑ D ∈ G.leftRightOverlapSources C x z, G.rectanglePentagonWeight C R D =
      ∑ E ∈ G.leftRightOverlapPartners C x z, G.pentagonRectangleWeight C R E := by
  classical
  rw [leftRightOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, leftRightOverlapPartner,
    pentagonRectangleWeight_recutLeftEqRight, Finset.sum_attach]

variable (x z) in
open scoped Classical in
/-- In an equation between the rectangle--pentagon sum and the pentagon--rectangle sum, each
augmented by further terms, the mixed `left = right` sources and their partners can be
removed. -/
theorem add_sum_rectanglePentagonWeight_eq_add_sum_iff_sdiff_leftRightOverlap
    [IsCancelAdd R] (A B : MvPolynomial (Fin n) R) :
    A + ∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D =
        B + ∑ E ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R E ↔
      A + ∑ D ∈ G.rectanglePentagonDecompositions C x z \ G.leftRightOverlapSources C x z,
          G.rectanglePentagonWeight C R D =
        B + ∑ E ∈ G.pentagonRectangleDecompositions C x z \ G.leftRightOverlapPartners C x z,
          G.pentagonRectangleWeight C R E := by
  rw [← Finset.sum_sdiff (G.leftRightOverlapSources_subset C)
      (f := G.rectanglePentagonWeight C R),
    ← Finset.sum_sdiff (G.leftRightOverlapPartners_subset C)
      (f := G.pentagonRectangleWeight C R),
    G.sum_rectanglePentagonWeight_leftRightOverlapSources_eq_sum_partners C x z R,
    ← add_assoc, ← add_assoc]
  exact add_right_cancel_iff

end TauCeti.GridDiagram
