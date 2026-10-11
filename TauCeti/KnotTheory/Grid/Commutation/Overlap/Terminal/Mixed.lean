/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Mixed.RightLeft
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Sum

/-!
# The mixed partners of terminal self-pairs

Consider a rectangle of the original diagram followed by a commutation pentagon turning on its
terminal side, which is the grid line `b = finRotate n a` replaced in the commutation.
`GridDiagram.terminalSelfPairs` collects the counted such domains whose two pieces share their
terminal side `b`, the rectangle starting strictly inside the pentagon's column interval, together
with their recuts, which are again rectangle--pentagon domains. This file identifies these recuts
without reference to the sources: they are exactly the counted mixed overlaps in which the
rectangle ends where the pentagon starts, with no other common side, and the turn row lies outside
the rows from the rectangle's top to the pentagon's top. These are the mixed `right = left`
overlaps that `GridDiagram.rightLeftOverlapSources` leaves out.

Write `p` and `q` for the rectangle's sides and `q`, `b` for the pentagon's. The two domains share
their bottom row. When the turn row lies outside the rows from the rectangle's top to the
pentagon's top, emptiness puts the rectangle's top row strictly between the common bottom row and
the pentagon's top row, with the turn row below it. The generic empty-rectangle recut then
consists of a rectangle ending on `b` spanning the rows from the rectangle's top to the
pentagon's top, followed by a rectangle ending on `b` spanning the rectangle's rows, which contain
the turn row. The second one is therefore a pentagon with the original pentagon's bottom row, so
the two composite domains cover the same squares with the same multiplicities and the recut is
counted; it is a terminal self-pair source, and the original domain is its partner
(`GridDiagram.mem_terminalSelfPairs_of_right_eq_left`).

Conversely, the turn row of a terminal self-pair source lies outside its rectangle's rows: the
pentagon's rows end where the rectangle's begin, and emptiness of the pentagon keeps the
rectangle's top row out of them
(`GridRectanglePentagonDecomposition.turn_notMem_cIco_rectangle_of_right_eq_right`). If a partner
of a source also satisfied the condition of `GridDiagram.rightLeftOverlapSources`, its recut,
which is the source, would be a pentagon followed by a rectangle, and the turn row would lie in the
source's rectangle. So the two descriptions agree
(`GridDiagram.mem_terminalSelfPairs_iff_sides`); in particular no terminal self-pair is a mixed
`right = left` source.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.turn_notMem_cIco_rectangle_of_right_eq_right`: the
  turn row of a terminal self-pair source lies outside its rectangle's rows.
* `TauCeti.GridDiagram.mem_terminalSelfPairs_of_right_eq_left`: a counted mixed `right = left`
  overlap outside `GridDiagram.rightLeftOverlapSources` is a terminal self-pair.
* `TauCeti.GridDiagram.mem_terminalSelfPairs_iff_sides`: the terminal self-pairs are the counted
  common-terminal-side sources and the counted mixed `right = left` overlaps sharing one side
  column whose turn row lies outside the rows from the rectangle's top to the pentagon's top.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- In a rectangle--pentagon domain whose two pieces share their terminal side, the rectangle
starting strictly inside the pentagon's column interval, the turn row lies outside the
rectangle's rows. -/
theorem turn_notMem_cIco_rectangle_of_right_eq_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hpentagon : D.pentagon.IsEmpty) :
    s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top := by
  -- The pentagon's rows end at the rectangle's bottom row.
  have htop : D.pentagon.top = D.rectangle.bottom := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.rectangle.map_right,
      GridRectangleBetween.bottom_def]
  -- The pentagon covers the column of the rectangle's initial side, where the intermediate state
  -- has the rectangle's top row; emptiness keeps that row out of the pentagon's rows.
  have hempty := (D.pentagon.isEmpty_iff_forall_notMem_cIoo).1 hpentagon _ hcol
  rw [D.rectangle.map_left, ← GridRectangleBetween.top_def, htop] at hempty
  have hturn := D.pentagon.turn_mem_cIco_bottom_top
  rw [htop] at hturn
  have hbottom : D.pentagon.bottom ≠ D.rectangle.top := by
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← D.rectangle.map_left]
    exact fun h => Grid.ne_left_of_mem_cIoo hcol (D.middle.toPerm.injective h).symm
  have hrect := D.rectangle.bottom_ne_top
  intro hs
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hturn hs hempty hbottom hrect
  split_ifs at hturn hs hempty <;> omega

/-- In a mixed `right = left` overlap with one common side whose turn row lies outside the rows
from the rectangle's top to the pentagon's top, both rectangles of the generic recut end on the
replaced line, and the second has the original pentagon's bottom row and contains the turn row. -/
private theorem rightLeftSelfRecut_geometry (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hother : D.rectangle.left ≠ D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.top D.pentagon.top) :
    let E := D.recutOfIsEmpty (D.hasOneCommonSide_of_right_eq_left hcommon hother)
      hrectangle hpentagon
    E.first.right = finRotate n a ∧ E.second.right = finRotate n a ∧
      E.second.bottom = D.pentagon.bottom ∧ s ∈ Grid.cIco E.second.bottom E.second.top := by
  intro E
  have hone := D.hasOneCommonSide_of_right_eq_left hcommon hother
  obtain ⟨hfb, hft, hst⟩ : D.toRectangleDecomposition.first.bottom = D.rectangle.bottom ∧
      D.toRectangleDecomposition.first.top = D.rectangle.top ∧
        D.toRectangleDecomposition.second.top = D.pentagon.top := by
    simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right, toRectangleDecomposition_middle, and_self]
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqLeft E := by
    simp only [E]
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.toRectangleDecomposition.isRecutOfRightEqLeft_recut
      (by simpa only [toRectangleDecomposition_first_right, toRectangleDecomposition_second_left]
        using hcommon) hone _ _
  obtain ⟨hEft, hEst⟩ := hdata.recut_sides
  rw [hst] at hEft
  rw [hft] at hEst
  -- The source state has the same row on `b` before and after the rectangle, since `b` is not a
  -- side of the rectangle: this row is the pentagon's top row.
  have hb : x (finRotate n a) = D.pentagon.top := by
    rw [GridRectangleBetween.top_def, D.pentagon.right_eq,
      D.rectangle.map_of_ne _ (D.pentagon.right_eq ▸ hother.symm)
        (hcommon ▸ D.pentagon.left_ne.symm)]
  have hright : E.first.right = finRotate n a :=
    x.toPerm.injective ((GridRectangleBetween.top_def _).symm.trans (hEft.trans hb.symm))
  -- The two domains share their bottom row, so the turn row lies in the rows from the
  -- rectangle's bottom to the pentagon's top.
  have hbottom : D.pentagon.bottom = D.rectangle.bottom := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, D.rectangle.map_right,
      GridRectangleBetween.bottom_def]
  have hturnWhole : s ∈ Grid.cIco D.rectangle.bottom D.pentagon.top := by
    simpa only [hbottom] using D.pentagon.turn_mem_cIco_bottom_top
  rcases hdata.recut_branch with ⟨hcol, hmiddle, -, hEsb⟩ | ⟨hcol, -, -, -⟩
  · -- The rectangle's top row lies between the common bottom row and the pentagon's top row,
    -- and the turn row lies below it, in the rows of the second recut rectangle.
    rw [hfb, hft, hst] at hcol
    rw [hft, hst] at hmiddle
    rw [hfb] at hEsb
    have hsecond : E.second.right = finRotate n a := by
      apply x.toPerm.injective
      have htop : x.swapRows D.rectangle.top D.pentagon.top E.second.right = D.rectangle.top :=
        (congrArg (fun y : GridState n => y E.second.right) hmiddle).symm.trans
          ((GridRectangleBetween.top_def _).symm.trans hEst)
      rw [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at htop
      exact htop.trans hb.symm
    have hs : s ∈ Grid.cIco D.rectangle.bottom D.rectangle.top := by
      rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol] at hturnWhole
      exact (Finset.mem_union.mp hturnWhole).resolve_right hturn
    exact ⟨hright, hsecond, hEsb.trans hbottom.symm, by rwa [hEsb, hEst]⟩
  · -- Otherwise the pentagon's top row lies inside the rectangle's rows, and the turn row lies
    -- in the rows from the rectangle's top to the pentagon's top.
    rw [hfb, hft, hst] at hcol
    exfalso
    simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hcol hturnWhole hturn
    split_ifs at hcol hturnWhole hturn <;> omega

/-- The recut of a mixed `right = left` overlap with one common side whose turn row lies outside
the rows from the rectangle's top to the pentagon's top, read as a rectangle followed by a
pentagon. -/
private noncomputable def rightLeftSelfRecut (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hother : D.rectangle.left ≠ D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.top D.pentagon.top) :
    GridRectanglePentagonDecomposition a s x z where
  middle := (D.recutOfIsEmpty (D.hasOneCommonSide_of_right_eq_left hcommon hother)
    hrectangle hpentagon).middle
  rectangle := (D.recutOfIsEmpty (D.hasOneCommonSide_of_right_eq_left hcommon hother)
    hrectangle hpentagon).first
  pentagon := GridPentagonBetween.ofRightEq
    (D.recutOfIsEmpty (D.hasOneCommonSide_of_right_eq_left hcommon hother)
      hrectangle hpentagon).second
    (D.rightLeftSelfRecut_geometry hcommon hother hrectangle hpentagon hturn).2.1
    (D.rightLeftSelfRecut_geometry hcommon hother hrectangle hpentagon hturn).2.2.2

/-- Forgetting the turn row of the promoted recut recovers the generic recut. -/
private theorem rightLeftSelfRecut_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hother : D.rectangle.left ≠ D.pentagon.right)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.rectangle.top D.pentagon.top) :
    (D.rightLeftSelfRecut hcommon hother hrectangle hpentagon hturn).toRectangleDecomposition =
      D.recutOfIsEmpty (D.hasOneCommonSide_of_right_eq_left hcommon hother)
        hrectangle hpentagon := by
  apply GridRectangleDecomposition.ext <;>
    simp [rightLeftSelfRecut,
      (D.rightLeftSelfRecut_geometry hcommon hother hrectangle hpentagon hturn).2.1]

end TauCeti.GridRectanglePentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted mixed `right = left` overlap with one common side whose turn row lies outside the
rows from the rectangle's top to the pentagon's top is a terminal self-pair: its recut is a
counted rectangle--pentagon domain whose two pieces share their terminal side, with the rectangle
starting strictly inside the pentagon's column interval. -/
theorem mem_terminalSelfPairs_of_right_eq_left
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (hcommon : D.rectangle.right = D.pentagon.left)
    (hother : D.rectangle.left ≠ D.pentagon.right)
    (hturn : C.turnRow ∉ Grid.cIco D.rectangle.top D.pentagon.top) :
    D ∈ G.terminalSelfPairs C x z := by
  obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hD
  have hrectangle := ((G.mem_unblockedRectangles _).1 hr).1
  have hpentagon := ((G.mem_pentagons _).1 hP).1
  have hone := D.hasOneCommonSide_of_right_eq_left hcommon hother
  obtain ⟨hfirstRight, hsecondRight, hbottom, -⟩ :=
    D.rightLeftSelfRecut_geometry hcommon hother hrectangle hpentagon hturn
  set E := D.rightLeftSelfRecut hcommon hother hrectangle hpentagon hturn
  have hErect := D.rightLeftSelfRecut_toRectangleDecomposition hcommon hother hrectangle
    hpentagon hturn
  have hrecut : D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition := by
    rw [hErect]
    exact D.isRecut_recutOfIsEmpty _ _ _
  have hfirst : D.toRectangleDecomposition.first.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_first_toGridRectangle] using hrectangle
  have hsecond : D.toRectangleDecomposition.second.IsEmpty := by
    simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
      using hpentagon
  have hback := hrecut.symm hone hfirst hsecond
  have hEone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (D.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  rw [← hErect] at hfirstRight hsecondRight hbottom
  have hEright : E.rectangle.right = finRotate n C.column := by
    simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right]
      using hfirstRight
  rw [mem_terminalSelfPairs]
  refine Or.inr ⟨E, (G.mem_terminalSelfPairSources C E).2 ⟨?_, ?_, ?_⟩, hback⟩
  · -- The recut covers the same squares as `D`, its pentagon having the same bottom row.
    refine G.mem_rectanglePentagonDecompositions_of_val_add_val_eq C hD
      (E.isEmpty_rectangle_of_isRecut hrecut) (E.isEmpty_pentagon_of_isRecut hrecut)
      (D.coveredSquares_val_add_val_eq_of_isRepartition_of_bottom_eq E hrecut.isRepartition ?_)
    simpa only [GridRectangleBetween.bottom_def,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_middle,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] using hbottom
  · exact hEright.trans E.pentagon.right_eq.symm
  · -- Recutting the common-terminal-side recut returns `D`, whose rectangle does not end on the
    -- replaced line; this fixes the column order of the recut.
    rcases hback.orientation with h | h | h | h
    · refine absurd ?_ (E.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hEone)
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, h.side_eq,
        hfirstRight, hsecondRight]
    · rcases h.recut_branch with ⟨hcol, -⟩ | ⟨-, -, hright, -⟩
      · simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
          hEright, ← E.pentagon.right_eq] using hcol
      · rw [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
          hfirstRight, hcommon] at hright
        exact absurd hright D.pentagon.left_ne
    · exact (E.toRectangleDecomposition.first.left_ne_right
        ((h.side_eq.trans hsecondRight).trans hfirstRight.symm)).elim
    · exact (E.toRectangleDecomposition.second.left_ne_right
        ((h.side_eq.symm.trans hfirstRight).trans hsecondRight.symm)).elim

/-- The terminal self-pairs are the counted rectangle--pentagon domains of two kinds: those whose
two pieces share their terminal side, the rectangle starting strictly inside the pentagon's column
interval; and those in which the rectangle ends where the pentagon starts, with no other common
side, and the turn row lies outside the rows from the rectangle's top to the pentagon's top. -/
theorem mem_terminalSelfPairs_iff_sides
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.terminalSelfPairs C x z ↔
      D ∈ G.rectanglePentagonDecompositions C x z ∧
        ((D.rectangle.right = D.pentagon.right ∧
            D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right) ∨
          (D.rectangle.right = D.pentagon.left ∧ D.rectangle.left ≠ D.pentagon.right ∧
            C.turnRow ∉ Grid.cIco D.rectangle.top D.pentagon.top)) := by
  constructor
  · intro hpair
    refine ⟨G.terminalSelfPairs_subset_rectanglePentagonDecompositions C hpair, ?_⟩
    rcases (G.mem_terminalSelfPairs C D).1 hpair with hsource | ⟨D₀, hD₀, hrecut⟩
    · exact Or.inl ((G.mem_terminalSelfPairSources C D).1 hsource).2
    right
    obtain ⟨hcounted₀, hcommon₀, hcol₀⟩ := (G.mem_terminalSelfPairSources C D₀).1 hD₀
    obtain ⟨hr₀, hP₀⟩ := (G.mem_rectanglePentagonDecompositions C D₀).1 hcounted₀
    have hpentagon₀ := ((G.mem_pentagons _).1 hP₀).1
    have hone₀ := D₀.hasOneCommonSide_of_right_eq_right hcommon₀ (Grid.ne_left_of_mem_cIoo hcol₀)
    have hsymm := hrecut.symm hone₀
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D₀.toRectangleDecomposition_first_toGridRectangle] using
          ((G.mem_unblockedRectangles _).1 hr₀).1)
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D₀.toRectangleDecomposition_middle, D₀.toRectangleDecomposition_second_toGridRectangle]
        using hpentagon₀)
    have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hsymm
      (D₀.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone₀)
    -- The common-terminal-side recut of the source ends the new rectangle where the new pentagon
    -- starts, on the source's initial rectangle side.
    have hcommon : D.rectangle.right = D.pentagon.left := by
      rcases hrecut.orientation with h | h | h | h
      · have hside := h.side_eq
        simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] at hside
        exact absurd hside (Grid.ne_left_of_mem_cIoo hcol₀)
      · obtain ⟨-, hleft⟩ := h.recut_sides
        rcases h.recut_branch with ⟨-, -, hright, -⟩ | ⟨hcol, -⟩
        · simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
            GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
            GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left] using
            hright.trans hleft.symm
        · simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
            GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
            GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
            hcommon₀] at hcol
          exact absurd (Grid.mem_cIoo_cyclic_right hcol)
            (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hcol₀)
      · have hside := h.side_eq
        simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right,
          ← hcommon₀] at hside
        exact absurd hside D₀.rectangle.left_ne_right
      · have hside := h.side_eq
        simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
          hcommon₀] at hside
        exact absurd hside.symm D₀.pentagon.left_ne_right
    have hother : D.rectangle.left ≠ D.pentagon.right := fun h =>
      D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hone (by
        simp only [GridRectangleBetween.sideColumns,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right, h, hcommon,
          Finset.pair_comm])
    obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1
      (G.terminalSelfPairs_subset_rectanglePentagonDecompositions C hpair)
    have hrectangle := ((G.mem_unblockedRectangles _).1 hr).1
    have hpentagon := ((G.mem_pentagons _).1 hP).1
    refine ⟨hcommon, hother, fun hturn => ?_⟩
    -- Otherwise the source would also be the pentagon--rectangle recut of `D`, whose pentagon
    -- contains the turn row, and the turn row would lie in the source's rectangle.
    have heq := (D.toRectangleDecomposition.existsUnique_isRecut hone
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle, D.toRectangleDecomposition_second_toGridRectangle]
        using hpentagon)).unique
      (D.isRecut_recutRightEqLeft hcommon hrectangle hpentagon hturn) hsymm
    have hleft := congrArg (fun E : GridRectangleDecomposition x z => E.first.left) heq
    have hright := congrArg (fun E : GridRectangleDecomposition x z => E.first.right) heq
    simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
      GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right] at hleft hright
    have hs := (D.recutRightEqLeft hcommon hrectangle hpentagon hturn).pentagon.turn_mem
    rw [hleft, hright] at hs
    exact D₀.turn_notMem_cIco_rectangle_of_right_eq_right hcommon₀ hcol₀ hpentagon₀
      (by rwa [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def])
  · rintro ⟨hD, hsource | ⟨hcommon, hother, hturn⟩⟩
    · exact (G.mem_terminalSelfPairs C D).2 (Or.inl
        ((G.mem_terminalSelfPairSources C D).2 ⟨hD, hsource⟩))
    · exact G.mem_terminalSelfPairs_of_right_eq_left C D hD hcommon hother hturn

end TauCeti.GridDiagram
