/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Weight
public import TauCeti.KnotTheory.Grid.Commutation.ChainMap
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Annulus.Weight
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# The diagonal coefficient of the commutation chain-map equation

Let `C` be a validated column commutation of a grid diagram, exchanging the column `a` with the
next column `b = finRotate n a`, with turn row `s`. The diagonal coefficient of the chain-map
equation `Φ ∘ ∂ = ∂' ∘ Φ` for the commutation map counts two-step domains from a grid state `x`
back to itself: a rectangle followed by a pentagon of either kind, or a pentagon of either kind
followed by a rectangle. Such a domain is a thin annulus, vertical or horizontal
(`Annulus/Basic.lean`, `InitialPentagon/Annulus/Basic.lean`), and each of the eight resulting
families has at most one counted element, determined by `x`.

* **Horizontal annuli.** They occupy the turn row. A rectangle followed by a pentagon turning on
  its terminal side, and a pentagon turning on its initial side followed by a rectangle, are both
  counted exactly when the row of `x` on the line `b` is `s` and the `X`-marking in row `s` lies
  in column `a`. The other two horizontal families are both counted exactly when the row of `x` on
  the line `b` is the successor of `s` and the `X`-marking in row `s` lies in column `b`. All four
  carry the variable of the `O`-marking in row `s`, so the horizontal terms cancel in pairs across
  the equation, over every coefficient semiring.
* **Vertical annuli.** Every vertical term covers squares of columns `a` and `b` only, cut at the
  turn row and at the row `p` of `x` on the line `b`. If `p = s`, only one vertical family on each
  side can occur, and the two are counted under the same marking condition with the same weight.
  Otherwise all four vertical families have the same marking condition and the same weight, and
  which of them occur depends only on the position of `s` relative to `p` and to the rows of `x`
  on the lines `a` and `finRotate n b`. The two families with a pentagon turning on its terminal
  side occur in complementary cases, and so do the two with a pentagon turning on its initial
  side. So, when counted, the vertical terms number two in total. They may lie on the same side of
  the equation, so they cancel only in characteristic two.

Hence the diagonal coefficients of `Φ ∘ ∂` and `∂' ∘ Φ` agree over every coefficient semiring of
characteristic two.

## Main results

All in the namespace `TauCeti.GridDiagram`:

* `sum_rectanglePentagonOppositeSideOrder_eq_sum_initialPentagonRectangleOppositeSideOrder` and
  `sum_rectangleInitialPentagonOppositeSideOrder_eq_sum_pentagonRectangleOppositeSideOrder`: the
  horizontal terms cancel in pairs.
* `sum_rectanglePentagonSameSideOrder_add_sum_rectangleInitialPentagonSameSideOrder`: the
  vertical terms cancel in characteristic two.
* `sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_self` and
  `commutationMap_unblockedDifferential_single_apply_self`: the diagonal coefficient identity of
  the commutation chain-map equation in characteristic two.

## References

This is Case (P-3) of the proof that the commutation map is a chain map in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, Figures 5.5--5.6; see
also Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  (R : Type*) [CommSemiring R]

/-! ### Vertical annuli

Each family below is evaluated in the same way. The side columns of both domains of a member are
determined by `x`, so the family has at most one member. Such a member is counted exactly when the
turn row lies among its pentagon's rows and the marking test of `Annulus/Vertical.lean` or
`InitialPentagon/Annulus/Vertical.lean` holds, and it is then built from column swaps of `x`. -/

open Classical in
/-- The vertical rectangle--pentagon term at `x` exists when the turn row lies between the rows of
`x` on the two commuted lines, from `b` up to `a`. -/
private theorem sum_rectanglePentagonSameSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.rectanglePentagonSameSideOrder C x, G.rectanglePentagonWeight C R D =
      if C.turnRow ∈ Grid.cIco (x (finRotate n C.column)) (x C.column) ∧
          G.X C.column ∈ insert C.turnRow (Grid.cIco (x (finRotate n C.column)) C.turnRow) ∧
            G.X (finRotate n C.column) ∉ Grid.cIco (x (finRotate n C.column)) C.turnRow then
        (if G.O C.column ∉ insert C.turnRow (Grid.cIco (x (finRotate n C.column)) C.turnRow)
          then MvPolynomial.X (finRotate n C.column) else 1) *
        (if G.O (finRotate n C.column) ∈ Grid.cIco (x (finRotate n C.column)) C.turnRow
          then MvPolynomial.X C.column else 1)
      else 0 := by
  -- Both domains of every term run between the lines `a` and `b`.
  have hgeom : ∀ D ∈ G.rectanglePentagonSameSideOrder C x,
      D.rectangle.left = C.column ∧ D.rectangle.right = finRotate n C.column ∧
        D.pentagon.left = C.column ∧ D.pentagon.right = finRotate n C.column ∧
          D.pentagon.bottom = x (finRotate n C.column) ∧ D.pentagon.top = x C.column := by
    intro D hD
    obtain ⟨hleft, hcol, -⟩ := (G.mem_rectanglePentagonSameSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_rectanglePentagonSameSideOrder C x D).1 hD).2.2
    refine ⟨hleft.trans hcol, hright.trans D.pentagon.right_eq, hcol, D.pentagon.right_eq, ?_, ?_⟩
    · rw [GridRectangleBetween.bottom_def, ← hleft, D.rectangle.map_left, hright,
        D.pentagon.right_eq]
    · rw [GridRectangleBetween.top_def, ← hright, D.rectangle.map_right, hleft, hcol]
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    let D₀ : GridRectanglePentagonDecomposition C.column C.turnRow x x :=
      ⟨x.swapColumns C.column (finRotate n C.column),
        GridRectangleBetween.ofSwapColumns _ _ _ _ C.column_ne_next rfl,
        GridPentagonBetween.ofRightEq
          (GridRectangleBetween.ofSwapColumns _ x _ _ C.column_ne_next
            (GridState.swapColumns_swapColumns _ _ x).symm)
          (GridRectangleBetween.ofSwapColumns_right ..) (by simpa using hs)⟩
    have hD₀ : D₀ ∈ G.rectanglePentagonSameSideOrder C x := by
      refine (G.mem_rectanglePentagonSameSideOrder_iff_markings C x D₀).2 ⟨?_, ?_, ?_⟩
      · simp [D₀]
      · simp [D₀]
      · simpa [D₀] using hX
    have huniq : ∀ D ∈ G.rectanglePentagonSameSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
      ext <;> simp only [GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
        GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right, *]
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.rectanglePentagonWeight_of_mem_rectanglePentagonSameSideOrder C R D₀ hD₀,
      (hgeom D₀ hD₀).2.2.2.2.1]
  next h =>
    refine Finset.sum_eq_zero fun D hD => (h ⟨?_, ?_⟩).elim
    · obtain ⟨-, -, -, -, hbottom, htop⟩ := hgeom D hD
      simpa only [hbottom, htop] using D.pentagon.turn_mem_cIco_bottom_top
    · simpa only [(hgeom D hD).2.2.2.2.1] using
        ((G.mem_rectanglePentagonSameSideOrder_iff_markings C x D).1 hD).2.2

open Classical in
/-- The vertical pentagon--rectangle term at `x` exists when the turn row lies between the rows of
`x` on the two commuted lines, from `a` up to `b`. -/
private theorem sum_pentagonRectangleSameSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.pentagonRectangleSameSideOrder C x, G.pentagonRectangleWeight C R D =
      if C.turnRow ∈ Grid.cIco (x C.column) (x (finRotate n C.column)) ∧
          G.X C.column ∉ Grid.cIoo C.turnRow (x (finRotate n C.column)) ∧
            G.X (finRotate n C.column) ∉ Grid.cIco (x (finRotate n C.column)) C.turnRow then
        (if G.O C.column ∈ Grid.cIoo C.turnRow (x (finRotate n C.column))
          then MvPolynomial.X (finRotate n C.column) else 1) *
        (if G.O (finRotate n C.column) ∈ Grid.cIco (x (finRotate n C.column)) C.turnRow
          then MvPolynomial.X C.column else 1)
      else 0 := by
  -- Both domains of every term run between the lines `a` and `b`.
  have hgeom : ∀ D ∈ G.pentagonRectangleSameSideOrder C x,
      D.pentagon.left = C.column ∧ D.pentagon.right = finRotate n C.column ∧
        D.rectangle.left = C.column ∧ D.rectangle.right = finRotate n C.column ∧
          D.pentagon.top = x (finRotate n C.column) ∧ D.pentagon.bottom = x C.column := by
    intro D hD
    obtain ⟨hleft, hcol, -⟩ := (G.mem_pentagonRectangleSameSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_pentagonRectangleSameSideOrder C x D).1 hD).2.2
    refine ⟨hcol, D.pentagon.right_eq, hleft.trans hcol, hright.trans D.pentagon.right_eq, ?_, ?_⟩
    · rw [GridRectangleBetween.top_def, D.pentagon.right_eq]
    · rw [GridRectangleBetween.bottom_def, hcol]
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    let D₀ : GridPentagonRectangleDecomposition C.column C.turnRow x x :=
      ⟨x.swapColumns C.column (finRotate n C.column),
        GridPentagonBetween.ofSwapColumns x C.column C.column_ne_next hs,
        GridRectangleBetween.ofSwapColumns _ x _ _ C.column_ne_next
          (GridState.swapColumns_swapColumns _ _ x).symm⟩
    have hD₀ : D₀ ∈ G.pentagonRectangleSameSideOrder C x := by
      refine (G.mem_pentagonRectangleSameSideOrder_iff_markings C x D₀).2 ⟨?_, ?_, ?_⟩
      · simp [D₀]
      · simp [D₀]
      · have htop : D₀.pentagon.top = x (finRotate n C.column) := by
          rw [GridRectangleBetween.top_def, D₀.pentagon.right_eq]
        rwa [htop]
    have huniq : ∀ D ∈ G.pentagonRectangleSameSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
      ext <;> simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right, *]
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.pentagonRectangleWeight_of_mem_pentagonRectangleSameSideOrder C R D₀ hD₀,
      (hgeom D₀ hD₀).2.2.2.2.1]
  next h =>
    refine Finset.sum_eq_zero fun D hD => (h ⟨?_, ?_⟩).elim
    · obtain ⟨-, -, -, -, htop, hbottom⟩ := hgeom D hD
      simpa only [hbottom, htop] using D.pentagon.turn_mem_cIco_bottom_top
    · simpa only [(hgeom D hD).2.2.2.2.1] using
        ((G.mem_pentagonRectangleSameSideOrder_iff_markings C x D).1 hD).2.2

open Classical in
/-- The vertical rectangle--initial-side pentagon term at `x` exists when the turn row lies
between the rows of `x` on the lines `finRotate n b` and `b`. -/
private theorem sum_rectangleInitialPentagonSameSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.rectangleInitialPentagonSameSideOrder C x, G.rectangleInitialPentagonWeight C R D =
      if C.turnRow ∈
            Grid.cIco (x (finRotate n (finRotate n C.column))) (x (finRotate n C.column)) ∧
          G.X C.column ∉ Grid.cIoo C.turnRow (x (finRotate n C.column)) ∧
            G.X (finRotate n C.column) ∉ Grid.cIco (x (finRotate n C.column)) C.turnRow then
        (if G.O C.column ∈ Grid.cIoo C.turnRow (x (finRotate n C.column))
          then MvPolynomial.X (finRotate n C.column) else 1) *
        (if G.O (finRotate n C.column) ∈ Grid.cIco (x (finRotate n C.column)) C.turnRow
          then MvPolynomial.X C.column else 1)
      else 0 := by
  -- Both domains of every term run between the lines `b` and `finRotate n b`.
  have hgeom : ∀ D ∈ G.rectangleInitialPentagonSameSideOrder C x,
      D.first.left = finRotate n C.column ∧
        D.first.right = finRotate n (finRotate n C.column) ∧
          D.second.left = finRotate n C.column ∧
            D.second.right = finRotate n (finRotate n C.column) ∧
              D.pentagon.top = x (finRotate n C.column) ∧
                D.pentagon.bottom = x (finRotate n (finRotate n C.column)) := by
    intro D hD
    obtain ⟨hleft, hthin, -⟩ :=
      (G.mem_rectangleInitialPentagonSameSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_rectangleInitialPentagonSameSideOrder C x D).1 hD).2.2
    have h₁ : D.first.left = finRotate n C.column := hleft.trans D.second_left_eq
    refine ⟨h₁, hthin.trans (congrArg _ h₁), D.second_left_eq,
      hright.symm.trans (hthin.trans (congrArg _ h₁)), ?_, ?_⟩
    · rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
        GridRectangleBetween.top_def, ← hright, D.first.map_right, h₁]
    · rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
        GridRectangleBetween.bottom_def, ← hleft, D.first.map_left, hthin, h₁]
  have hne : finRotate n C.column ≠ finRotate n (finRotate n C.column) :=
    (Grid.finRotate_ne_self (C.one_lt) _).symm
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    let D₀ : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x :=
      ⟨⟨x.swapColumns (finRotate n C.column) (finRotate n (finRotate n C.column)),
          GridRectangleBetween.ofSwapColumns _ _ _ _ hne rfl,
          GridRectangleBetween.ofSwapColumns _ x _ _ hne
            (GridState.swapColumns_swapColumns _ _ x).symm⟩,
        GridRectangleBetween.ofSwapColumns_left .., by simpa using hs⟩
    have hD₀ : D₀ ∈ G.rectangleInitialPentagonSameSideOrder C x := by
      refine (G.mem_rectangleInitialPentagonSameSideOrder_iff_markings C x D₀).2 ⟨?_, ?_, ?_⟩
      · simp [D₀]
      · simp [D₀]
      · simpa [D₀, GridRectangleBetween.top_def] using hX
    have huniq : ∀ D ∈ G.rectangleInitialPentagonSameSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      exact GridRectangleInitialPentagonDecomposition.ext (GridRectangleDecomposition.ext
        (h₁.trans h₁'.symm) (h₂.trans h₂'.symm) (h₃.trans h₃'.symm) (h₄.trans h₄'.symm))
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.rectangleInitialPentagonWeight_of_mem_rectangleInitialPentagonSameSideOrder C R D₀ hD₀,
      (hgeom D₀ hD₀).2.2.2.2.1]
  next h =>
    refine Finset.sum_eq_zero fun D hD => (h ⟨?_, ?_⟩).elim
    · obtain ⟨-, -, -, -, htop, hbottom⟩ := hgeom D hD
      simpa only [hbottom, htop] using D.pentagon.turn_mem_cIco_bottom_top
    · simpa only [(hgeom D hD).2.2.2.2.1] using
        ((G.mem_rectangleInitialPentagonSameSideOrder_iff_markings C x D).1 hD).2.2

open Classical in
/-- The vertical initial-side pentagon--rectangle term at `x` exists when the turn row lies
between the rows of `x` on the lines `b` and `finRotate n b`. -/
private theorem sum_initialPentagonRectangleSameSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.initialPentagonRectangleSameSideOrder C x, G.initialPentagonRectangleWeight C R D =
      if C.turnRow ∈
            Grid.cIco (x (finRotate n C.column)) (x (finRotate n (finRotate n C.column))) ∧
          G.X C.column ∈ insert C.turnRow (Grid.cIco (x (finRotate n C.column)) C.turnRow) ∧
            G.X (finRotate n C.column) ∉ Grid.cIco (x (finRotate n C.column)) C.turnRow then
        (if G.O C.column ∉ insert C.turnRow (Grid.cIco (x (finRotate n C.column)) C.turnRow)
          then MvPolynomial.X (finRotate n C.column) else 1) *
        (if G.O (finRotate n C.column) ∈ Grid.cIco (x (finRotate n C.column)) C.turnRow
          then MvPolynomial.X C.column else 1)
      else 0 := by
  -- Both domains of every term run between the lines `b` and `finRotate n b`.
  have hgeom : ∀ D ∈ G.initialPentagonRectangleSameSideOrder C x,
      D.first.left = finRotate n C.column ∧
        D.first.right = finRotate n (finRotate n C.column) ∧
          D.second.left = finRotate n C.column ∧
            D.second.right = finRotate n (finRotate n C.column) ∧
              D.pentagon.bottom = x (finRotate n C.column) ∧
                D.pentagon.top = x (finRotate n (finRotate n C.column)) := by
    intro D hD
    obtain ⟨hleft, hthin, -⟩ :=
      (G.mem_initialPentagonRectangleSameSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_initialPentagonRectangleSameSideOrder C x D).1 hD).2.2
    have h₂ : D.first.right = finRotate n (finRotate n C.column) := by
      rw [hthin, D.first_left_eq]
    refine ⟨D.first_left_eq, h₂, hleft.trans D.first_left_eq, hright.trans h₂, ?_, ?_⟩
    · rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
        GridRectangleBetween.bottom_def, D.first_left_eq]
    · rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
        GridRectangleBetween.top_def, h₂]
  have hne : finRotate n C.column ≠ finRotate n (finRotate n C.column) :=
    (Grid.finRotate_ne_self (C.one_lt) _).symm
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    let D₀ : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x :=
      ⟨⟨x.swapColumns (finRotate n C.column) (finRotate n (finRotate n C.column)),
          GridRectangleBetween.ofSwapColumns _ _ _ _ hne rfl,
          GridRectangleBetween.ofSwapColumns _ x _ _ hne
            (GridState.swapColumns_swapColumns _ _ x).symm⟩,
        GridRectangleBetween.ofSwapColumns_left .., by simpa using hs⟩
    have hD₀ : D₀ ∈ G.initialPentagonRectangleSameSideOrder C x := by
      refine (G.mem_initialPentagonRectangleSameSideOrder_iff_markings C x D₀).2 ⟨?_, ?_, ?_⟩
      · simp [D₀]
      · simp [D₀]
      · simpa [D₀, GridRectangleBetween.bottom_def] using hX
    have huniq : ∀ D ∈ G.initialPentagonRectangleSameSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      exact GridInitialPentagonRectangleDecomposition.ext (GridRectangleDecomposition.ext
        (h₁.trans h₁'.symm) (h₂.trans h₂'.symm) (h₃.trans h₃'.symm) (h₄.trans h₄'.symm))
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.initialPentagonRectangleWeight_of_mem_initialPentagonRectangleSameSideOrder C R D₀ hD₀,
      (hgeom D₀ hD₀).2.2.2.2.1]
  next h =>
    refine Finset.sum_eq_zero fun D hD => (h ⟨?_, ?_⟩).elim
    · obtain ⟨-, -, -, -, hbottom, htop⟩ := hgeom D hD
      simpa only [hbottom, htop] using D.pentagon.turn_mem_cIco_bottom_top
    · simpa only [(hgeom D hD).2.2.2.2.1] using
        ((G.mem_initialPentagonRectangleSameSideOrder_iff_markings C x D).1 hD).2.2

/-! ### Horizontal annuli

As for the vertical annuli, each family has at most one member: its rectangle and pentagon have
the side columns `b` and the line on which `x` sits one row above, or one row below, its row on
`b`. -/

open Classical in
/-- The horizontal rectangle--pentagon term at `x` exists when the row of `x` on the line `b` is
the turn row. -/
private theorem sum_rectanglePentagonOppositeSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.rectanglePentagonOppositeSideOrder C x, G.rectanglePentagonWeight C R D =
      if x (finRotate n C.column) = C.turnRow ∧ G.X C.column = C.turnRow then
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow))
      else 0 := by
  -- The rectangle starts on `b` and ends on the line where `x` sits one row higher.
  have hgeom : ∀ D ∈ G.rectanglePentagonOppositeSideOrder C x,
      D.rectangle.left = finRotate n C.column ∧ D.pentagon.right = finRotate n C.column ∧
        D.pentagon.left = D.rectangle.right ∧
          x D.rectangle.right = finRotate n (x (finRotate n C.column)) ∧
            x (finRotate n C.column) = C.turnRow := by
    intro D hD
    obtain ⟨hleft, hthin, -⟩ :=
      (G.mem_rectanglePentagonOppositeSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_rectanglePentagonOppositeSideOrder C x D).1 hD).2.2
    have h₁ : D.rectangle.left = finRotate n C.column := hleft.trans D.pentagon.right_eq
    have htop : x D.rectangle.right = finRotate n (x (finRotate n C.column)) := by
      rw [← D.rectangle.top_def, hthin, D.rectangle.bottom_def, h₁]
    have hbottom : D.pentagon.bottom = x (finRotate n C.column) := by
      rw [GridRectangleBetween.bottom_def, ← hright, D.rectangle.map_right, h₁]
    have hPtop : D.pentagon.top = x D.rectangle.right := by
      rw [GridRectangleBetween.top_def, ← hleft, D.rectangle.map_left]
    refine ⟨h₁, D.pentagon.right_eq, hright.symm, htop, ?_⟩
    rw [← hbottom]
    exact (D.pentagon.turn_eq_bottom_of_top_eq_finRotate_bottom
      (by rw [hPtop, hbottom, htop])).symm
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    have hn := C.one_lt
    have hd := x.apply_transpose_apply (finRotate n C.turnRow)
    have hbd : finRotate n C.column ≠ x.transpose (finRotate n C.turnRow) :=
      fun h => Grid.finRotate_ne_self hn _ (hd.symm.trans ((congrArg x.toPerm h).symm.trans hs))
    let D₀ : GridRectanglePentagonDecomposition C.column C.turnRow x x :=
      ⟨x.swapColumns (finRotate n C.column) (x.transpose (finRotate n C.turnRow)),
        GridRectangleBetween.ofSwapColumns _ _ _ _ hbd rfl,
        GridPentagonBetween.ofRightEq
          (GridRectangleBetween.ofSwapColumns _ x _ _ hbd.symm
            (by rw [GridState.swapColumns_comm _ _ x, GridState.swapColumns_swapColumns]))
          (GridRectangleBetween.ofSwapColumns_right ..) (by
            simp only [GridRectangleBetween.ofSwapColumns_bottom,
              GridRectangleBetween.ofSwapColumns_top, GridState.swapColumns_apply,
              Equiv.swap_apply_left, Equiv.swap_apply_right, hd, hs]
            exact Grid.left_mem_cIco (Grid.finRotate_ne_self hn _).symm)⟩
    have hD₀ : D₀ ∈ G.rectanglePentagonOppositeSideOrder C x := by
      refine (G.mem_rectanglePentagonOppositeSideOrder_iff_markings C x D₀).2 ⟨?_, ?_, hX⟩
      · simp [D₀]
      · simp only [D₀, GridRectangleBetween.ofSwapColumns_top,
          GridRectangleBetween.ofSwapColumns_bottom, hd, hs]
    have huniq : ∀ D ∈ G.rectanglePentagonOppositeSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      have hr : D.rectangle.right = D₀.rectangle.right := x.toPerm.injective (h₄.trans h₄'.symm)
      apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
      exact GridRectangleDecomposition.ext (by simp only [
          GridRectanglePentagonDecomposition.toRectangleDecomposition_first_left, h₁, h₁'])
        (by simpa only [
          GridRectanglePentagonDecomposition.toRectangleDecomposition_first_right] using hr)
        (by simpa only [GridRectanglePentagonDecomposition.toRectangleDecomposition_second_left,
          h₃, h₃'] using hr)
        (by simp only [
          GridRectanglePentagonDecomposition.toRectangleDecomposition_second_right, h₂, h₂'])
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.rectanglePentagonWeight_of_mem_rectanglePentagonOppositeSideOrder C R D₀ hD₀]
  next h =>
    exact Finset.sum_eq_zero fun D hD => (h ⟨(hgeom D hD).2.2.2.2,
      G.X_column_eq_turnRow_of_mem_rectanglePentagonOppositeSideOrder C x D hD⟩).elim

open Classical in
/-- The horizontal initial-side pentagon--rectangle term at `x` exists when the row of `x` on the
line `b` is the turn row. -/
private theorem sum_initialPentagonRectangleOppositeSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.initialPentagonRectangleOppositeSideOrder C x,
        G.initialPentagonRectangleWeight C R D =
      if x (finRotate n C.column) = C.turnRow ∧ G.X C.column = C.turnRow then
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow))
      else 0 := by
  -- The pentagon starts on `b` and ends on the line where `x` sits one row higher.
  have hgeom : ∀ D ∈ G.initialPentagonRectangleOppositeSideOrder C x,
      D.first.left = finRotate n C.column ∧ D.second.right = finRotate n C.column ∧
        D.second.left = D.first.right ∧
          x D.first.right = finRotate n (x (finRotate n C.column)) ∧
            x (finRotate n C.column) = C.turnRow := by
    intro D hD
    obtain ⟨hleft, hthin, -⟩ :=
      (G.mem_initialPentagonRectangleOppositeSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_initialPentagonRectangleOppositeSideOrder C x D).1 hD).2.2
    have htop : x D.first.right = finRotate n (x (finRotate n C.column)) := by
      rw [← D.first.top_def, hthin, D.first.bottom_def, D.first_left_eq]
    refine ⟨D.first_left_eq, hright.trans D.first_left_eq, hleft, htop, ?_⟩
    have hturn := D.pentagon.turn_eq_bottom_of_top_eq_finRotate_bottom (by
      simpa only [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
        using hthin)
    rw [GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
      GridRectangleBetween.bottom_def, D.first_left_eq] at hturn
    exact hturn.symm
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    have hn := C.one_lt
    have hf := x.apply_transpose_apply (finRotate n C.turnRow)
    have hbf : finRotate n C.column ≠ x.transpose (finRotate n C.turnRow) :=
      fun h => Grid.finRotate_ne_self hn _ (hf.symm.trans ((congrArg x.toPerm h).symm.trans hs))
    let D₀ : GridInitialPentagonRectangleDecomposition C.column C.turnRow x x :=
      ⟨⟨x.swapColumns (finRotate n C.column)
            (x.transpose (finRotate n C.turnRow)),
          GridRectangleBetween.ofSwapColumns _ _ _ _ hbf rfl,
          GridRectangleBetween.ofSwapColumns _ x _ _ hbf.symm
            (by rw [GridState.swapColumns_comm _ _ x, GridState.swapColumns_swapColumns])⟩,
        GridRectangleBetween.ofSwapColumns_left .., by
          simp only [GridRectangleBetween.ofSwapColumns_bottom,
            GridRectangleBetween.ofSwapColumns_top, hf, hs]
          exact Grid.left_mem_cIco (Grid.finRotate_ne_self hn _).symm⟩
    have hD₀ : D₀ ∈ G.initialPentagonRectangleOppositeSideOrder C x := by
      refine (G.mem_initialPentagonRectangleOppositeSideOrder_iff_markings C x D₀).2
        ⟨?_, ?_, hX⟩
      · simp [D₀]
      · simp only [D₀, GridRectangleBetween.ofSwapColumns_top,
          GridRectangleBetween.ofSwapColumns_bottom, hf, hs]
    have huniq : ∀ D ∈ G.initialPentagonRectangleOppositeSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      have hr : D.first.right = D₀.first.right := x.toPerm.injective (h₄.trans h₄'.symm)
      exact GridInitialPentagonRectangleDecomposition.ext (GridRectangleDecomposition.ext
        (h₁.trans h₁'.symm) hr (h₃.trans (hr.trans h₃'.symm)) (h₂.trans h₂'.symm))
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.initialPentagonRectangleWeight_of_mem_initialPentagonRectangleOppositeSideOrder C R D₀ hD₀]
  next h =>
    exact Finset.sum_eq_zero fun D hD => (h ⟨(hgeom D hD).2.2.2.2,
      G.X_column_eq_turnRow_of_mem_initialPentagonRectangleOppositeSideOrder C x D hD⟩).elim

open Classical in
/-- The horizontal rectangle--initial-side pentagon term at `x` exists when the row of `x` on the
line `b` is the successor of the turn row. -/
private theorem sum_rectangleInitialPentagonOppositeSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.rectangleInitialPentagonOppositeSideOrder C x,
        G.rectangleInitialPentagonWeight C R D =
      if x (finRotate n C.column) = finRotate n C.turnRow ∧
          G.X (finRotate n C.column) = C.turnRow then
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow))
      else 0 := by
  -- The rectangle ends on `b` and starts on the line where `x` sits in the turn row.
  have hgeom : ∀ D ∈ G.rectangleInitialPentagonOppositeSideOrder C x,
      D.first.right = finRotate n C.column ∧ D.second.left = finRotate n C.column ∧
        D.second.right = D.first.left ∧ x D.first.left = C.turnRow ∧
          x (finRotate n C.column) = finRotate n C.turnRow := by
    intro D hD
    obtain ⟨hleft, hthin, -⟩ :=
      (G.mem_rectangleInitialPentagonOppositeSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_rectangleInitialPentagonOppositeSideOrder C x D).1 hD).2.2
    have h₁ : D.first.right = finRotate n C.column := hright.trans D.second_left_eq
    have hbottom : D.pentagon.bottom = x D.first.left := by
      rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
        GridRectangleBetween.bottom_def, ← hright, D.first.map_right]
    have htop : D.pentagon.top = x (finRotate n C.column) := by
      rw [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
        GridRectangleBetween.top_def, ← hleft, D.first.map_left, h₁]
    have hthin' : x (finRotate n C.column) = finRotate n (x D.first.left) := by
      rw [← h₁, ← D.first.top_def, hthin, D.first.bottom_def]
    have hturn := D.pentagon.turn_eq_bottom_of_top_eq_finRotate_bottom
      (by rw [htop, hbottom, hthin'])
    rw [hbottom] at hturn
    exact ⟨h₁, D.second_left_eq, hleft.symm, hturn.symm, hturn ▸ hthin'⟩
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    have hn := C.one_lt
    have hc := x.apply_transpose_apply C.turnRow
    have hcb : x.transpose C.turnRow ≠ finRotate n C.column := fun h =>
      Grid.finRotate_ne_self hn C.turnRow (hs.symm.trans (h ▸ hc))
    let D₀ : GridRectangleInitialPentagonDecomposition C.column C.turnRow x x :=
      ⟨⟨x.swapColumns (x.transpose C.turnRow) (finRotate n C.column),
          GridRectangleBetween.ofSwapColumns _ _ _ _ hcb rfl,
          GridRectangleBetween.ofSwapColumns _ x _ _ hcb.symm
            (by rw [GridState.swapColumns_comm _ _ x, GridState.swapColumns_swapColumns])⟩,
        GridRectangleBetween.ofSwapColumns_left .., by
          simp only [GridRectangleBetween.ofSwapColumns_bottom,
            GridRectangleBetween.ofSwapColumns_top, GridState.swapColumns_apply,
            Equiv.swap_apply_left, Equiv.swap_apply_right, hc, hs]
          exact Grid.left_mem_cIco (Grid.finRotate_ne_self hn _).symm⟩
    have hD₀ : D₀ ∈ G.rectangleInitialPentagonOppositeSideOrder C x := by
      refine (G.mem_rectangleInitialPentagonOppositeSideOrder_iff_markings C x D₀).2
        ⟨?_, ?_, hX⟩
      · simp [D₀]
      · simp only [D₀, GridRectangleBetween.ofSwapColumns_top,
          GridRectangleBetween.ofSwapColumns_bottom, hc, hs]
    have huniq : ∀ D ∈ G.rectangleInitialPentagonOppositeSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      have hl : D.first.left = D₀.first.left := x.toPerm.injective (h₄.trans h₄'.symm)
      exact GridRectangleInitialPentagonDecomposition.ext (GridRectangleDecomposition.ext
        hl (h₁.trans h₁'.symm) (h₂.trans h₂'.symm) (h₃.trans (hl.trans h₃'.symm)))
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.rectangleInitialPentagonWeight_of_mem_rectangleInitialPentagonOppositeSideOrder C R D₀
        hD₀]
  next h =>
    exact Finset.sum_eq_zero fun D hD => (h ⟨(hgeom D hD).2.2.2.2,
      G.X_next_eq_turnRow_of_mem_rectangleInitialPentagonOppositeSideOrder C x D hD⟩).elim

open Classical in
/-- The horizontal pentagon--rectangle term at `x` exists when the row of `x` on the line `b` is
the successor of the turn row. -/
private theorem sum_pentagonRectangleOppositeSideOrder_eq (x : GridState n) :
    ∑ D ∈ G.pentagonRectangleOppositeSideOrder C x, G.pentagonRectangleWeight C R D =
      if x (finRotate n C.column) = finRotate n C.turnRow ∧
          G.X (finRotate n C.column) = C.turnRow then
        MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) (G.O.transpose C.turnRow))
      else 0 := by
  -- The pentagon ends on `b` and starts on the line where `x` sits in the turn row.
  have hgeom : ∀ D ∈ G.pentagonRectangleOppositeSideOrder C x,
      D.pentagon.right = finRotate n C.column ∧ D.rectangle.left = finRotate n C.column ∧
        D.rectangle.right = D.pentagon.left ∧ x D.pentagon.left = C.turnRow ∧
          x (finRotate n C.column) = finRotate n C.turnRow := by
    intro D hD
    obtain ⟨hleft, hthin, -⟩ :=
      (G.mem_pentagonRectangleOppositeSideOrder_iff_markings C x D).1 hD
    have hright := ((G.mem_pentagonRectangleOppositeSideOrder C x D).1 hD).2.2
    have hturn := D.pentagon.turn_eq_bottom_of_top_eq_finRotate_bottom hthin
    rw [GridRectangleBetween.bottom_def] at hturn
    refine ⟨D.pentagon.right_eq, hleft.trans D.pentagon.right_eq, hright, hturn.symm, ?_⟩
    rw [← D.pentagon.right_eq, ← GridRectangleBetween.top_def, hthin,
      GridRectangleBetween.bottom_def, ← hturn]
  split
  next h =>
    obtain ⟨hs, hX⟩ := h
    have hn := C.one_lt
    have hc := x.apply_transpose_apply C.turnRow
    have hcb : x.transpose C.turnRow ≠ finRotate n C.column := fun h =>
      Grid.finRotate_ne_self hn C.turnRow (hs.symm.trans (h ▸ hc))
    let D₀ : GridPentagonRectangleDecomposition C.column C.turnRow x x :=
      ⟨x.swapColumns (x.transpose C.turnRow) (finRotate n C.column),
        GridPentagonBetween.ofSwapColumns x _ hcb (by
          rw [hc, hs]
          exact Grid.left_mem_cIco (Grid.finRotate_ne_self hn _).symm),
        GridRectangleBetween.ofSwapColumns _ x _ _ hcb.symm
          (by rw [GridState.swapColumns_comm _ _ x, GridState.swapColumns_swapColumns])⟩
    have hD₀ : D₀ ∈ G.pentagonRectangleOppositeSideOrder C x := by
      refine (G.mem_pentagonRectangleOppositeSideOrder_iff_markings C x D₀).2 ⟨?_, ?_, hX⟩
      · rw [D₀.pentagon.right_eq]
        simp [D₀]
      · rw [GridRectangleBetween.top_def, GridRectangleBetween.bottom_def, D₀.pentagon.right_eq]
        simp only [D₀, GridPentagonBetween.ofSwapColumns_left, hc, hs]
    have huniq : ∀ D ∈ G.pentagonRectangleOppositeSideOrder C x, D = D₀ := by
      intro D hD
      obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hgeom D hD
      obtain ⟨h₁', h₂', h₃', h₄', -⟩ := hgeom D₀ hD₀
      have hl : D.pentagon.left = D₀.pentagon.left := x.toPerm.injective (h₄.trans h₄'.symm)
      apply GridPentagonRectangleDecomposition.toRectangleDecomposition_injective
      exact GridRectangleDecomposition.ext (by
          simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left]
            using hl)
        (by simp only [
          GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right, h₁, h₁'])
        (by simp only [
          GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left, h₂, h₂'])
        (by simpa only [
          GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right, h₃, h₃']
            using hl)
    rw [Finset.sum_eq_single_of_mem D₀ hD₀ fun D hD hne => (hne (huniq D hD)).elim,
      G.pentagonRectangleWeight_of_mem_pentagonRectangleOppositeSideOrder C R D₀ hD₀]
  next h =>
    exact Finset.sum_eq_zero fun D hD => (h ⟨(hgeom D hD).2.2.2.2,
      G.X_next_eq_turnRow_of_mem_pentagonRectangleOppositeSideOrder C x D hD⟩).elim

/-! ### The diagonal coefficient -/

/-- The horizontal annular terms made of a rectangle followed by a pentagon turning on its terminal
side, and those made of a pentagon turning on its initial side followed by a rectangle, contribute
equally to the two sides of the commutation chain-map equation: both exist exactly when the row of
`x` on the replaced line is the turn row, both are counted exactly when the `X`-marking in the turn
row lies in the first commuted column, and both carry the variable of the turn row's `O`-marking. -/
theorem sum_rectanglePentagonOppositeSideOrder_eq_sum_initialPentagonRectangleOppositeSideOrder
    (x : GridState n) :
    ∑ D ∈ G.rectanglePentagonOppositeSideOrder C x, G.rectanglePentagonWeight C R D =
      ∑ D ∈ G.initialPentagonRectangleOppositeSideOrder C x,
        G.initialPentagonRectangleWeight C R D := by
  rw [G.sum_rectanglePentagonOppositeSideOrder_eq C R x,
    G.sum_initialPentagonRectangleOppositeSideOrder_eq C R x]

/-- The horizontal annular terms made of a rectangle followed by a pentagon turning on its initial
side, and those made of a pentagon turning on its terminal side followed by a rectangle, contribute
equally to the two sides of the commutation chain-map equation: both exist exactly when the row of
`x` on the replaced line is the successor of the turn row, both are counted exactly when the
`X`-marking in the turn row lies in the second commuted column, and both carry the variable of the
turn row's `O`-marking. -/
theorem sum_rectangleInitialPentagonOppositeSideOrder_eq_sum_pentagonRectangleOppositeSideOrder
    (x : GridState n) :
    ∑ D ∈ G.rectangleInitialPentagonOppositeSideOrder C x,
        G.rectangleInitialPentagonWeight C R D =
      ∑ D ∈ G.pentagonRectangleOppositeSideOrder C x, G.pentagonRectangleWeight C R D := by
  rw [G.sum_rectangleInitialPentagonOppositeSideOrder_eq C R x,
    G.sum_pentagonRectangleOppositeSideOrder_eq C R x]

/-- In characteristic two, the vertical annular terms contribute equally to the two sides of the
commutation chain-map equation. When the row of `x` on the replaced line is the turn row, at most
one term occurs on each side, and the two have the same marking condition and weight. Otherwise
all four terms share one marking condition and one weight, and occur in two complementary
pairs. -/
theorem sum_rectanglePentagonSameSideOrder_add_sum_rectangleInitialPentagonSameSideOrder
    [CharP R 2] (x : GridState n) :
    ∑ D ∈ G.rectanglePentagonSameSideOrder C x, G.rectanglePentagonWeight C R D +
        ∑ D ∈ G.rectangleInitialPentagonSameSideOrder C x,
          G.rectangleInitialPentagonWeight C R D =
      ∑ D ∈ G.pentagonRectangleSameSideOrder C x, G.pentagonRectangleWeight C R D +
        ∑ D ∈ G.initialPentagonRectangleSameSideOrder C x,
          G.initialPentagonRectangleWeight C R D := by
  rw [G.sum_rectanglePentagonSameSideOrder_eq C R x,
    G.sum_rectangleInitialPentagonSameSideOrder_eq C R x,
    G.sum_pentagonRectangleSameSideOrder_eq C R x,
    G.sum_initialPentagonRectangleSameSideOrder_eq C R x]
  have hab : x C.column ≠ x (finRotate n C.column) := fun h =>
    C.column_ne_next (x.toPerm.injective h)
  have hbb : x (finRotate n (finRotate n C.column)) ≠ x (finRotate n C.column) := fun h =>
    Grid.finRotate_ne_self (C.one_lt) _ (x.toPerm.injective h)
  by_cases hp : x (finRotate n C.column) = C.turnRow
  · -- Only the terms whose pentagon starts in the turn row survive, one on each side.
    rw [hp] at hab hbb ⊢
    simp only [Grid.left_mem_cIco hab.symm, Grid.left_mem_cIco hbb.symm, Grid.right_notMem_cIco,
      true_and, false_and, ↓reduceIte, add_zero, zero_add]
  · -- The four terms share one marking condition and one weight, and come in complementary
    -- pairs.
    simp only [Grid.mem_insert_cIco_iff_notMem_cIoo hp, not_not,
      ← Grid.notMem_cIco_iff_mem_cIco_swap hab.symm, ← Grid.notMem_cIco_iff_mem_cIco_swap hbb]
    have key (P Q B : Prop) [Decidable P] [Decidable Q] [Decidable B] (W : MvPolynomial (Fin n) R) :
        ((if P ∧ B then W else 0) + if Q ∧ B then W else 0) =
          (if ¬P ∧ B then W else 0) + if ¬Q ∧ B then W else 0 := by
      by_cases hP : P <;> by_cases hQ : Q <;> by_cases hB : B <;>
        simp [hP, hQ, hB, CharTwo.add_self_eq_zero]
    exact key _ _ _ _

/-- The diagonal coefficient identity of the commutation chain-map equation: in characteristic
two, the counted two-step domains from a grid state back to itself made of a rectangle followed by
a pentagon of either kind, and those made of a pentagon of either kind followed by a rectangle,
have the same total weight. -/
theorem sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_self [CharP R 2]
    (x : GridState n) :
    (∑ D ∈ G.rectanglePentagonDecompositions C x x, G.rectanglePentagonWeight C R D) +
        ∑ D ∈ G.rectangleInitialPentagonDecompositions C x x,
          G.rectangleInitialPentagonWeight C R D =
      (∑ D ∈ G.pentagonRectangleDecompositions C x x, G.pentagonRectangleWeight C R D) +
        ∑ D ∈ G.initialPentagonRectangleDecompositions C x x,
          G.initialPentagonRectangleWeight C R D := by
  rw [G.sum_rectanglePentagonDecompositions_self C x,
    G.sum_rectangleInitialPentagonDecompositions_self C x,
    G.sum_pentagonRectangleDecompositions_self C x,
    G.sum_initialPentagonRectangleDecompositions_self C x,
    G.sum_rectanglePentagonOppositeSideOrder_eq_sum_initialPentagonRectangleOppositeSideOrder C R x,
    G.sum_rectangleInitialPentagonOppositeSideOrder_eq_sum_pentagonRectangleOppositeSideOrder C R x]
  have hvertical :=
    G.sum_rectanglePentagonSameSideOrder_add_sum_rectangleInitialPentagonSameSideOrder C R x
  calc _ = (∑ D ∈ G.rectanglePentagonSameSideOrder C x, G.rectanglePentagonWeight C R D +
          ∑ D ∈ G.rectangleInitialPentagonSameSideOrder C x,
            G.rectangleInitialPentagonWeight C R D) +
        (∑ D ∈ G.initialPentagonRectangleOppositeSideOrder C x,
            G.initialPentagonRectangleWeight C R D +
          ∑ D ∈ G.pentagonRectangleOppositeSideOrder C x, G.pentagonRectangleWeight C R D) := by
        abel
    _ = _ := by
      rw [hvertical]
      abel

/-- In characteristic two, the commutation map commutes with the unblocked differentials on the
diagonal: the coefficient of a grid state `x` in the image of `x` is the same for `Φ ∘ ∂` and
`∂' ∘ Φ`. -/
theorem commutationMap_unblockedDifferential_single_apply_self [CharP R 2] (x : GridState n) :
    G.commutationMap R C (G.unblockedDifferential R (Finsupp.single x 1)) x =
      (G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R
        (G.commutationMap R C (Finsupp.single x 1)) x := by
  rw [G.commutationMap_unblockedDifferential_single_apply C R x x,
    G.unblockedDifferential_commutationMap_single_apply C R x x]
  exact G.sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_self C R x

end TauCeti.GridDiagram
