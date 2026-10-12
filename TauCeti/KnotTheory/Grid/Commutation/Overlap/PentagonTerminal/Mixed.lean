/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.PentagonTerminal.Sum

/-!
# The mixed partners of pentagon--rectangle terminal self-pairs

Consider a commutation pentagon turning on its terminal side, which is the grid line
`b = finRotate n a` replaced in the commutation, followed by a rectangle of the commuted diagram.
`GridDiagram.pentagonTerminalSelfPairs` collects the counted such domains whose two pieces share
their terminal side `b`, the rectangle starting strictly inside the pentagon's column interval,
together with their recuts (`GridPentagonRectangleDecomposition.recutTerminal`), which are again
pentagon--rectangle domains. This file identifies these recuts without reference to the sources:
they are exactly the counted mixed overlaps in which the rectangle ends where the pentagon starts,
with no other common side, and the turn row lies outside the rows from the pentagon's bottom to
the rectangle's bottom.

Write `q`, `b` for the pentagon's sides and `p`, `q` for the rectangle's. The two domains share
their top row, the row of the source state on `b`. When the turn row lies outside the rows from
the pentagon's bottom to the rectangle's bottom, emptiness puts the rectangle's bottom row strictly
between the pentagon's bottom and top rows, with the turn row above it. The generic empty-rectangle
recut then consists of a rectangle ending on `b` spanning the rows from the rectangle's bottom to
the common top row, which contain the turn row, followed by a rectangle ending on `b` spanning the
rows from the pentagon's bottom to the rectangle's bottom. The first one is therefore a pentagon,
the two pieces share their terminal side `b`, and the original domain is the terminal self-recut
of this source; so the source covers the same squares with the same multiplicities and is counted
(`GridDiagram.mem_pentagonTerminalSelfPairs_of_right_eq_left`).

Conversely, the turn row of a terminal self-pair source lies outside its rectangle's rows: the
rectangle's rows end where the pentagon's begin, and emptiness of the pentagon keeps the
rectangle's bottom row out of them
(`GridPentagonRectangleDecomposition.turn_notMem_cIco_rectangle_of_right_eq_right`). Reading the
rows of the terminal self-recut off `GridPentagonRectangleDecomposition.recutTerminal_geometry`
then shows that every partner is of the kind above, so the two descriptions agree
(`GridDiagram.mem_pentagonTerminalSelfPairs_iff_sides`).

## Main results

* `TauCeti.GridPentagonRectangleDecomposition.turn_notMem_cIco_rectangle_of_right_eq_right`: the
  turn row of a terminal self-pair source lies outside its rectangle's rows.
* `TauCeti.GridDiagram.mem_pentagonTerminalSelfPairs_of_right_eq_left`: a counted mixed
  `right = left` overlap whose turn row lies outside the rows from the pentagon's bottom to the
  rectangle's bottom is a terminal self-pair.
* `TauCeti.GridDiagram.mem_pentagonTerminalSelfPairs_iff_sides`: the terminal self-pairs are the
  counted common-terminal-side sources and the counted mixed `right = left` overlaps sharing one
  side column whose turn row lies outside the rows from the pentagon's bottom to the rectangle's
  bottom.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).

This file adapts the rectangle--pentagon formalization in
`TauCeti.KnotTheory.Grid.Commutation.Overlap.Terminal.Mixed`
(`GridDiagram.mem_terminalSelfPairs_iff_sides`).
-/

public section

namespace TauCeti.GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The rectangle's rows end at the pentagon's bottom row when the two pieces share their terminal
side. -/
private theorem rectangle_top_eq_pentagon_bottom (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right) : D.rectangle.top = D.pentagon.bottom := by
  rw [GridRectangleBetween.top_def, hcommon, D.pentagon.map_right,
    GridRectangleBetween.bottom_def]

/-- In a pentagon--rectangle domain whose two pieces share their terminal side, the rectangle
starting strictly inside the pentagon's column interval, the turn row lies outside the
rectangle's rows. -/
theorem turn_notMem_cIco_rectangle_of_right_eq_right
    (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hpentagon : D.pentagon.IsEmpty) :
    s ∉ Grid.cIco D.rectangle.bottom D.rectangle.top := by
  -- The rectangle's bottom row is the row of the source state in a column covered by the
  -- pentagon; emptiness keeps that row out of the pentagon's rows.
  have hbottom : D.rectangle.bottom = x D.rectangle.left := by
    rw [GridRectangleBetween.bottom_def,
      D.pentagon.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol) (Grid.ne_right_of_mem_cIoo hcol)]
  have hempty := (D.pentagon.isEmpty_iff_forall_notMem_cIoo).1 hpentagon _ hcol
  rw [← hbottom] at hempty
  have hne₁ : D.rectangle.bottom ≠ D.pentagon.bottom := by
    rw [hbottom, GridRectangleBetween.bottom_def]
    exact fun h => Grid.ne_left_of_mem_cIoo hcol (x.toPerm.injective h)
  have hne₂ : D.rectangle.bottom ≠ D.pentagon.top := by
    rw [hbottom, GridRectangleBetween.top_def]
    exact fun h => Grid.ne_right_of_mem_cIoo hcol (x.toPerm.injective h)
  have hturn := D.pentagon.turn_mem_cIco_bottom_top
  have hne₃ := D.pentagon.bottom_ne_top
  rw [D.rectangle_top_eq_pentagon_bottom hcommon]
  intro hs
  simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hturn hs hempty hne₁ hne₂ hne₃
  split_ifs at hturn hs hempty <;> omega

/-- In a mixed `right = left` overlap with one common side whose turn row lies outside the rows
from the pentagon's bottom to the rectangle's bottom, both rectangles of the generic recut end on
the replaced line, and the first contains the turn row. -/
private theorem rightLeftSelfRecut_geometry (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hturn : s ∉ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    (E.toRectangleDecomposition.recut hone hfirst hsecond).first.right = finRotate n a ∧
      (E.toRectangleDecomposition.recut hone hfirst hsecond).second.right = finRotate n a ∧
        s ∈ Grid.cIco (E.toRectangleDecomposition.recut hone hfirst hsecond).first.bottom
          (E.toRectangleDecomposition.recut hone hfirst hsecond).first.top := by
  set D := E.toRectangleDecomposition.recut hone hfirst hsecond
  obtain ⟨hfb, hft, hsb⟩ : E.toRectangleDecomposition.first.bottom = E.pentagon.bottom ∧
      E.toRectangleDecomposition.first.top = E.pentagon.top ∧
        E.toRectangleDecomposition.second.bottom = E.rectangle.bottom := by
    simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_left, toRectangleDecomposition_middle, and_self]
  have hdata : E.toRectangleDecomposition.IsRecutOfLeftEqRight D :=
    E.toRectangleDecomposition.isRecutOfLeftEqRight_recut
      (by simpa only [toRectangleDecomposition_first_left,
        toRectangleDecomposition_second_right] using hcommon.symm) hone hfirst hsecond
  obtain ⟨hDfb, -⟩ := hdata.recut_sides
  rw [hsb] at hDfb
  -- The source state has the pentagon's top row on `b`.
  have hb : x (finRotate n a) = E.pentagon.top := by
    rw [GridRectangleBetween.top_def, E.pentagon.right_eq]
  have hturnP := E.pentagon.turn_mem_cIco_bottom_top
  rcases hdata.recut_branch with ⟨hrow, -⟩ | ⟨hrow, hmiddle, hDft, hDst⟩
  · -- Otherwise the pentagon's rows lie in the rows from its bottom to the rectangle's bottom,
    -- turn row included.
    rw [hfb, hft, hsb] at hrow
    exfalso
    simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hrow hturn hturnP
    split_ifs at hrow hturn hturnP <;> omega
  · -- The rectangle's bottom row lies strictly inside the pentagon's rows, and the turn row lies
    -- above it, in the rows of the first recut rectangle.
    rw [hsb, hfb, hft] at hrow
    rw [hsb, hft] at hmiddle
    rw [hft] at hDft
    rw [hsb] at hDst
    have hfirstRight : D.first.right = finRotate n a :=
      x.toPerm.injective ((GridRectangleBetween.top_def _).symm.trans (hDft.trans hb.symm))
    have hsecondRight : D.second.right = finRotate n a := by
      apply x.toPerm.injective
      have htop : x.swapRows E.rectangle.bottom E.pentagon.top D.second.right =
          E.rectangle.bottom :=
        (congrArg (fun y : GridState n => y D.second.right) hmiddle).symm.trans
          ((GridRectangleBetween.top_def _).symm.trans hDst)
      rw [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at htop
      exact htop.trans hb.symm
    have hs : s ∈ Grid.cIco E.rectangle.bottom E.pentagon.top := by
      rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow] at hturnP
      exact (Finset.mem_union.mp hturnP).resolve_left hturn
    exact ⟨hfirstRight, hsecondRight, by rwa [hDfb, hDft]⟩

/-- The recut of a mixed `right = left` overlap with one common side whose turn row lies outside
the rows from the pentagon's bottom to the rectangle's bottom, read as a pentagon followed by a
rectangle. -/
private noncomputable def rightLeftSelfRecut (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hturn : s ∉ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    GridPentagonRectangleDecomposition a s x z where
  middle := (E.toRectangleDecomposition.recut hone hfirst hsecond).middle
  pentagon := GridPentagonBetween.ofRightEq
    (E.toRectangleDecomposition.recut hone hfirst hsecond).first
    (E.rightLeftSelfRecut_geometry hcommon hone hfirst hsecond hturn).1
    (E.rightLeftSelfRecut_geometry hcommon hone hfirst hsecond hturn).2.2
  rectangle := (E.toRectangleDecomposition.recut hone hfirst hsecond).second

/-- Forgetting the turn row of the promoted recut recovers the generic recut. -/
private theorem rightLeftSelfRecut_toRectangleDecomposition
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hturn : s ∉ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    (E.rightLeftSelfRecut hcommon hone hfirst hsecond hturn).toRectangleDecomposition =
      E.toRectangleDecomposition.recut hone hfirst hsecond := by
  apply GridRectangleDecomposition.ext <;>
    simp [rightLeftSelfRecut,
      (E.rightLeftSelfRecut_geometry hcommon hone hfirst hsecond hturn).1]

/-- The promoted recut recuts the original domain. -/
private theorem isRecut_rightLeftSelfRecut (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hturn : s ∉ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    E.toRectangleDecomposition.IsRecut
      (E.rightLeftSelfRecut hcommon hone hfirst hsecond hturn).toRectangleDecomposition := by
  rw [E.rightLeftSelfRecut_toRectangleDecomposition]
  exact E.toRectangleDecomposition.isRecut_recut _ _ _

/-- The two pieces of the promoted recut share their terminal side, the rectangle starting
strictly inside the pentagon's column interval. Recutting it returns `E`, whose pentagon ends on
the replaced line; this fixes the column order. -/
private theorem rightLeftSelfRecut_terminal_overlap
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hturn : s ∉ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    let D := E.rightLeftSelfRecut hcommon hone hfirst hsecond hturn
    D.rectangle.right = D.pentagon.right ∧
      D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right := by
  intro D
  obtain ⟨hfirstRight, hsecondRight, -⟩ :=
    E.rightLeftSelfRecut_geometry hcommon hone hfirst hsecond hturn
  rw [← E.rightLeftSelfRecut_toRectangleDecomposition hcommon hone hfirst hsecond hturn]
    at hfirstRight hsecondRight
  have hback := (E.isRecut_rightLeftSelfRecut hcommon hone hfirst hsecond hturn).symm
    hone hfirst hsecond
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  refine ⟨by simpa only [toRectangleDecomposition_second_right, ← D.pentagon.right_eq] using
    hsecondRight, ?_⟩
  rcases hback.orientation with h | h | h | h
  · refine absurd ?_ (D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hDone)
    rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, h.side_eq,
      hfirstRight, hsecondRight]
  · rcases h.recut_branch with ⟨-, -, hright, -⟩ | ⟨hcol, -⟩
    · rw [toRectangleDecomposition_first_right, E.pentagon.right_eq] at hright
      exact absurd (hright.symm.trans hfirstRight.symm)
        D.toRectangleDecomposition.first.left_ne_right
    · simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left,
        toRectangleDecomposition_first_right] using hcol
  · exact (D.toRectangleDecomposition.first.left_ne_right
      ((h.side_eq.trans hsecondRight).trans hfirstRight.symm)).elim
  · exact (D.toRectangleDecomposition.second.left_ne_right
      ((h.side_eq.symm.trans hfirstRight).trans hsecondRight.symm)).elim

end TauCeti.GridPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted mixed `right = left` pentagon--rectangle overlap with one common side whose turn row
lies outside the rows from the pentagon's bottom to the rectangle's bottom is a terminal self-pair:
it is the terminal self-recut of a counted pentagon--rectangle domain whose two pieces share their
terminal side, with the rectangle starting strictly inside the pentagon's column interval. -/
theorem mem_pentagonTerminalSelfPairs_of_right_eq_left
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hother : E.rectangle.left ≠ E.pentagon.right)
    (hturn : C.turnRow ∉ Grid.cIco E.pentagon.bottom E.rectangle.bottom) :
    E ∈ G.pentagonTerminalSelfPairs C x z := by
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
  have hfirst := E.underlying_first_isEmpty ((G.mem_pentagons _).1 hP).1
  have hsecond := E.underlying_second_isEmpty
    (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1
  have hone := E.toRectangleDecomposition.hasOneCommonSide_of_left_eq_right
    (by simpa using hcommon.symm) (by simpa using hother.symm)
  set D := E.rightLeftSelfRecut hcommon hone hfirst hsecond hturn
  have hrecut := E.isRecut_rightLeftSelfRecut hcommon hone hfirst hsecond hturn
  have hback := hrecut.symm hone hfirst hsecond
  have hDpentagon := D.isEmpty_pentagon_of_isRecut hrecut
  have hDrectangle := D.isEmpty_rectangle_of_isRecut hrecut
  obtain ⟨hDcommon, hDcol⟩ :=
    E.rightLeftSelfRecut_terminal_overlap hcommon hone hfirst hsecond hturn
  -- `E` is the terminal self-recut of `D`, so the two cover the same squares and `D` is counted.
  have hcovered := D.coveredSquares_val_add_recutTerminal hDcommon hDcol hDpentagon hDrectangle
  rw [D.recutTerminal_eq_of_isRecut hDcommon hDcol hDpentagon hDrectangle hback] at hcovered
  refine (G.mem_pentagonTerminalSelfPairs C E).2 (Or.inr ⟨D,
    (G.mem_pentagonTerminalSelfPairSources C D).2 ⟨?_, hDcommon, hDcol⟩, hback⟩)
  exact G.mem_pentagonRectangleDecompositions_of_val_add_val_eq_pentagonRectangle C hE
    hDpentagon hDrectangle hcovered.symm

/-- The terminal self-pairs of the pentagon--rectangle sum are the counted pentagon--rectangle
domains of two kinds: those whose two pieces share their terminal side, the rectangle starting
strictly inside the pentagon's column interval; and those in which the rectangle ends where the
pentagon starts, with no other common side, and the turn row lies outside the rows from the
pentagon's bottom to the rectangle's bottom. -/
theorem mem_pentagonTerminalSelfPairs_iff_sides
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.pentagonTerminalSelfPairs C x z ↔
      E ∈ G.pentagonRectangleDecompositions C x z ∧
        ((E.rectangle.right = E.pentagon.right ∧
            E.rectangle.left ∈ Grid.cIoo E.pentagon.left E.pentagon.right) ∨
          (E.rectangle.right = E.pentagon.left ∧ E.rectangle.left ≠ E.pentagon.right ∧
            C.turnRow ∉ Grid.cIco E.pentagon.bottom E.rectangle.bottom)) := by
  constructor
  · intro hpair
    refine ⟨G.pentagonTerminalSelfPairs_subset_pentagonRectangleDecompositions C hpair, ?_⟩
    rcases (G.mem_pentagonTerminalSelfPairs C E).1 hpair with hsource | ⟨D, hD, hrecut⟩
    · exact Or.inl ((G.mem_pentagonTerminalSelfPairSources C E).1 hsource).2
    right
    obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_pentagonTerminalSelfPairSources C D).1 hD
    obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C D).1 hcounted
    have hpentagon := ((G.mem_pentagons _).1 hP).1
    have hrectangle :=
      (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1
    -- `E` is the terminal self-recut of `D`, whose geometry is known.
    have hself := D.recutTerminal_eq_of_isRecut hcommon hcol hpentagon hrectangle hrecut
    obtain ⟨hmiddle, hPleft, hPbottom, -, hrleft, hrright⟩ :=
      D.recutTerminal_geometry hcommon hcol hpentagon hrectangle
    rw [hself] at hmiddle hPleft hPbottom hrleft hrright
    have hne := Grid.ne_left_of_mem_cIoo hcol
    have hne' := Grid.ne_right_of_mem_cIoo hcol
    -- The rectangle of `E` starts in the row of the pentagon of `D` on its initial side.
    have hrbottom : E.rectangle.bottom = D.pentagon.bottom := by
      rw [GridRectangleBetween.bottom_def, hrleft, hmiddle, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hne)
          (D.pentagon.right_eq ▸ D.pentagon.left_ne), GridRectangleBetween.bottom_def]
    refine ⟨hrright.trans hPleft.symm, ?_, ?_⟩
    · rw [hrleft, E.pentagon.right_eq, ← D.pentagon.right_eq]
      exact D.pentagon.left_ne_right
    · have hturn := D.turn_notMem_cIco_rectangle_of_right_eq_right hcommon hcol hpentagon
      rwa [hPbottom, hrbottom, ← D.rectangle_top_eq_pentagon_bottom hcommon]
  · rintro ⟨hE, hsource | ⟨hcommon, hother, hturn⟩⟩
    · exact (G.mem_pentagonTerminalSelfPairs C E).2 (Or.inl
        ((G.mem_pentagonTerminalSelfPairSources C E).2 ⟨hE, hsource⟩))
    · exact G.mem_pentagonTerminalSelfPairs_of_right_eq_left C E hE hcommon hother hturn

end TauCeti.GridDiagram
