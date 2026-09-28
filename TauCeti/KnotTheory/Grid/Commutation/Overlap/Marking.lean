/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic

/-!
# The promoted pentagon of a common-initial-side overlap carries no new marking

Let `D` be a two-step domain made of a rectangle followed by a pentagon, and let the pentagon's
initial side be the rectangle's initial side: the common-initial-side overlap of a column
commutation. `TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic` recuts along that side and
promotes the first new rectangle to a pentagon, so that the two contributions of a square of the
differential can be paired.

Pairing also needs the promoted pentagon to be a pentagon of the same kind as the original one, that
is to carry no `X`-marking. The covered-square repartition proved in `Overlap/Basic.lean` is one of
the two *underlying rectangles*, and a pentagon covers only part of its underlying rectangle: in the
two columns next to the replaced grid line its turn row cuts the covered arc. The pentagon-level
statement is therefore its own, and it does follow from the geometry. The promoted pentagon spans
either a sub-arc of the original pentagon's column arc with the same rows, or the same column arc
with the rows extended back through the original rectangle's row arc to its initial row. Its
covered squares lie in the union of the squares covered by the original pentagon and by the
original rectangle
(`coveredSquares_pentagon_subset_recutLeftEqLeft`), so a marking avoided by both is avoided by the
promoted pentagon (`disjoint_coveredSquares_XSet_pentagon_recutLeftEqLeft`).

The two recut branches are read off from the side data. In the first, the original rectangle's
terminal side lies strictly inside the original pentagon's column arc: the promoted pentagon spans
the terminal part of that arc, between that side and the replaced grid line, with the original
pentagon's rows, and covers a subset of the original pentagon's squares. In the second, the
replaced grid line lies strictly inside the original rectangle's column arc: the promoted pentagon
spans the original pentagon's whole column arc but reaches back through the original rectangle's
row arc to its initial row, and the band of squares it adds along that row arc comes out of the
original rectangle.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.pentagon_toGridRectangle_recutLeftEqLeft`: the
  promoted pentagon is the recut's first rectangle read as a pentagon.
* `TauCeti.GridRectanglePentagonDecomposition.pentagon_left_bottom_recutLeftEqLeft`,
  `pentagon_top_recutLeftEqLeft`: its sides.
* `TauCeti.GridRectanglePentagonDecomposition.coveredSquares_pentagon_subset_recutLeftEqLeft`:
  the squares it covers are covered by the original pentagon or by the original rectangle.
* `TauCeti.GridRectanglePentagonDecomposition.
  disjoint_coveredSquares_XSet_pentagon_recutLeftEqLeft`: it carries no `X`-marking when
  neither of the two original domains carries one.

## References

The pairing of the two contributions in the chain-map equation of a column commutation is that of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1. The recut hexagon is
cut the other way, and the pentagon of the new pairing must be one of the empty pentagons carrying
no `X`-marking that the pentagon map of `TauCeti.KnotTheory.Grid.Commutation.Pentagon` counts.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The side data of the recut along a common initial side: either the original rectangle's
terminal side lies strictly inside the original pentagon's column arc, and the recut's first
rectangle starts there, or the replaced grid line lies strictly inside the original rectangle's
column arc, and the recut's first rectangle starts at the common initial side. -/
private theorem isRecutOfLeftEqLeft_branch
    (D : GridRectanglePentagonDecomposition a s x z)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hcommon : D.rectangle.left = D.pentagon.left) :
    (D.rectangle.right ∈ Grid.cIoo D.rectangle.left D.pentagon.right ∧
        (D.recutOfIsEmpty hone hrectangle hpentagon).first.left = D.rectangle.right) ∨
      (D.pentagon.right ∈ Grid.cIoo D.rectangle.left D.rectangle.right ∧
        (D.recutOfIsEmpty hone hrectangle hpentagon).first.left = D.rectangle.left) := by
  have hdata : D.toRectangleDecomposition.IsRecutOfLeftEqLeft
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.toRectangleDecomposition.isRecutOfLeftEqLeft_recut
      (by
      simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
        hcommon) hone _ _
  rcases hdata.recut_branch with ⟨hcol, -, hleft, -⟩ | ⟨hcol, -, hleft, -⟩
  · refine Or.inl ⟨?_, ?_⟩
    · simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right] using hcol
    · simpa only [toRectangleDecomposition_first_right] using hleft
  · refine Or.inr ⟨?_, ?_⟩
    · simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right] using hcol
    · simpa only [toRectangleDecomposition_first_left] using hleft

/-- The underlying toroidal rectangle of the promoted pentagon is that of the recut's first
rectangle. -/
@[simp]
theorem pentagon_toGridRectangle_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.toGridRectangle =
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.toGridRectangle := by
  rw [D.recutOfIsEmpty_eq_recut]
  have h := congrArg (fun w : GridRectangleDecomposition x z => w.first.toGridRectangle)
    (D.recutLeftEqLeft_toRectangleDecomposition hcommon hone hrectangle hpentagon)
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle]
    using h

/-- The common initial side of the two domains is not the replaced grid line. -/
private theorem finRotate_ne_rectangle_left (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left) :
    finRotate n a ≠ D.rectangle.left :=
  fun h => D.pentagon.left_ne (h.trans hcommon).symm

/-- The bottom row of the original pentagon is the top row of the original rectangle: at their
common side the intermediate state has the row the source has on the rectangle's terminal side. -/
private theorem pentagon_bottom_eq_rectangle_top
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left) :
    D.pentagon.bottom = D.rectangle.top := by
  rw [GridRectangleBetween.bottom_def, ← hcommon, D.rectangle.map_left,
    ← GridRectangleBetween.top_def]

/-- The top row of the original pentagon is the row the source has on the replaced grid line. -/
private theorem pentagon_top_eq (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left) (hne : finRotate n a ≠ D.rectangle.right) :
    D.pentagon.top = x (finRotate n a) := by
  rw [GridRectangleBetween.top_def, D.pentagon.right_eq]
  exact D.rectangle.map_of_ne _ (D.finRotate_ne_rectangle_left hcommon) hne

/-- The three sides of the promoted pentagon are the sides of the recut's first rectangle. -/
private theorem pentagon_sides_of_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.left =
        (D.recutOfIsEmpty hone hrectangle hpentagon).first.left ∧
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.bottom =
        (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom ∧
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.top =
        (D.recutOfIsEmpty hone hrectangle hpentagon).first.top := by
  have h := D.pentagon_toGridRectangle_recutLeftEqLeft hcommon hone hrectangle hpentagon
  refine ⟨?_, ?_, ?_⟩
  · simpa only [GridRectangleBetween.toGridRectangle_left] using congrArg GridRectangle.left h
  · simpa only [GridRectangleBetween.toGridRectangle_bottom] using congrArg GridRectangle.bottom h
  · simpa only [GridRectangleBetween.toGridRectangle_top] using congrArg GridRectangle.top h

/-- The initial side and the bottom row of the promoted pentagon: the terminal side and terminal
row of the original rectangle in the first recut branch, and its initial side and initial row in
the second. -/
theorem pentagon_left_bottom_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.left = D.rectangle.right ∧
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.bottom = D.rectangle.top ∨
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.left = D.rectangle.left ∧
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.bottom =
        D.rectangle.bottom := by
  have hsides := D.pentagon_sides_of_recutLeftEqLeft hcommon hone hrectangle hpentagon
  rcases D.isRecutOfLeftEqLeft_branch hone hrectangle hpentagon hcommon with ⟨-, hleft⟩ | ⟨-, hleft⟩
  · refine Or.inl ⟨?_, ?_⟩
    · exact hsides.1.trans hleft
    · rw [hsides.2.1, GridRectangleBetween.bottom_def, hleft]
      exact D.rectangle.top_def.symm
  · refine Or.inr ⟨?_, ?_⟩
    · exact hsides.1.trans hleft
    · rw [hsides.2.1, GridRectangleBetween.bottom_def, hleft]
      exact D.rectangle.bottom_def.symm

/-- The top row of the promoted pentagon is the top row of the original pentagon, in either recut
branch. -/
@[simp]
theorem pentagon_top_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.top = D.pentagon.top := by
  have hright := D.recut_first_right_of_left_eq_left hcommon hone hrectangle hpentagon
  rw [(D.recutOfIsEmpty_eq_recut hone hrectangle hpentagon).symm] at hright
  refine ?_
  rw [(D.pentagon_sides_of_recutLeftEqLeft hcommon hone hrectangle hpentagon).2.2,
    GridRectangleBetween.top_def, hright,
    D.pentagon_top_eq hcommon ?_]
  rcases D.isRecutOfLeftEqLeft_branch hone hrectangle hpentagon hcommon with ⟨hcol, -⟩ | ⟨hcol, -⟩
  · exact fun h => (Grid.ne_right_of_mem_cIoo hcol) (h.symm.trans D.pentagon.right_eq.symm)
  · exact fun h => (Grid.ne_right_of_mem_cIoo hcol).symm (h.symm.trans D.pentagon.right_eq.symm)

/-- In the first recut branch the promoted pentagon covers a subset of the squares covered by the
original pentagon: it spans the terminal part of the original pentagon's column arc, between the
original rectangle's terminal side and the replaced grid line, and has the original pentagon's
rows. -/
private theorem mem_coveredSquares_pentagon_of_branch1
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hcol : D.rectangle.right ∈ Grid.cIoo D.rectangle.left D.pentagon.right)
    (hleft : (D.recutOfIsEmpty hone hrectangle hpentagon).first.left = D.rectangle.right)
    (p : Fin n × Fin n) :
    p ∈ (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.coveredSquares →
      p ∈ D.pentagon.coveredSquares := by
  intro hp
  have hsides := D.pentagon_sides_of_recutLeftEqLeft hcommon hone hrectangle hpentagon
  have hbottom : (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.bottom =
      D.pentagon.bottom := by
    rw [hsides.2.1, GridRectangleBetween.bottom_def, hleft]
    exact D.rectangle.top_def.symm.trans (D.pentagon_bottom_eq_rectangle_top hcommon).symm
  have htop := D.pentagon_top_recutLeftEqLeft hcommon hone hrectangle hpentagon
  rcases (GridPentagonBetween.mem_coveredSquares
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon p).mp hp with h | h | h
  · rw [hsides.1, hleft, hbottom, htop, D.pentagon.right_eq.symm] at h
    refine (GridPentagonBetween.mem_coveredSquares D.pentagon p).2 (Or.inl ⟨h.1, ?_, h.2.2⟩)
    simpa only [hcommon, D.pentagon.right_eq] using Grid.cIco_subset_of_mem_cIoo hcol h.2.1
  · rw [htop] at h
    exact (GridPentagonBetween.mem_coveredSquares D.pentagon p).2 (Or.inr (Or.inl ⟨h.1, h.2⟩))
  · rw [hbottom] at h
    exact (GridPentagonBetween.mem_coveredSquares D.pentagon p).2 (Or.inr (Or.inr ⟨h.1, h.2⟩))

/-- In the second recut branch the promoted pentagon spans the whole column arc of the original
pentagon but reaches back through the original rectangle's row arc to its initial row; the band of
squares it adds along that row arc comes out of the original rectangle. -/
private theorem mem_coveredSquares_pentagon_of_branch2
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hcol : D.pentagon.right ∈ Grid.cIoo D.rectangle.left D.rectangle.right)
    (hleft : (D.recutOfIsEmpty hone hrectangle hpentagon).first.left = D.rectangle.left)
    (p : Fin n × Fin n) :
    p ∈ (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.coveredSquares →
      p ∈ D.pentagon.coveredSquares ∪ D.rectangle.toGridRectangle.coveredSquares := by
  intro hp
  have hsides := D.pentagon_sides_of_recutLeftEqLeft hcommon hone hrectangle hpentagon
  have hPleft : (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.left =
      D.rectangle.left := hsides.1.trans hleft
  have hPbottom : (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.bottom =
      D.rectangle.bottom := by
    rw [hsides.2.1, GridRectangleBetween.bottom_def, hleft]
    exact D.rectangle.bottom_def.symm
  have hPtop := D.pentagon_top_recutLeftEqLeft hcommon hone hrectangle hpentagon
  have hspan : Grid.cIco D.rectangle.left D.pentagon.right ⊆
      Grid.cIco D.rectangle.left D.rectangle.right :=
    fun q hq => Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hq hcol
  have hrect (q : Fin n × Fin n) (hcolumn : q.1 ∈ Grid.cIco D.rectangle.left D.rectangle.right)
      (hrow : q.2 ∈ Grid.cIco D.rectangle.bottom D.rectangle.top) :
      q ∈ D.rectangle.toGridRectangle.coveredSquares := by
    refine (GridRectangle.mem_coveredSquares D.rectangle.toGridRectangle q).2 ⟨?_, ?_⟩
    · simpa only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right] using hcolumn
    · simpa only [GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top] using hrow
  rcases (GridPentagonBetween.mem_coveredSquares
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon p).mp hp with h | h | h
  · rw [hPleft, hPbottom, hPtop] at h
    by_cases hrow : p.2 ∈ Grid.cIco D.pentagon.bottom D.pentagon.top
    · refine Finset.mem_union.mpr (Or.inl
        ((GridPentagonBetween.mem_coveredSquares D.pentagon p).2 (Or.inl ⟨h.1, ?_, hrow⟩)))
      simpa only [hcommon] using h.2.1
    · refine Finset.mem_union.mpr (Or.inr (hrect p ?_ ?_))
      · have hcolumn : p.1 ∈ Grid.cIco D.rectangle.left D.pentagon.right := by
          simpa only [D.pentagon.right_eq] using h.2.1
        exact hspan hcolumn
      · have hsplit : p.2 ∈ Grid.cIco D.pentagon.bottom D.pentagon.top ∨
            p.2 ∈ Grid.cIco D.rectangle.bottom D.pentagon.bottom :=
          Finset.mem_union.mp
            (Grid.cIco_subset_cIco_union_cIco (t := D.rectangle.bottom)
              (w := D.pentagon.bottom) (u := D.pentagon.top) h.2.2)
        rcases hsplit with hfirst | hsecond
        · exact (hrow hfirst).elim
        · rw [D.pentagon_bottom_eq_rectangle_top hcommon] at hsecond
          exact hsecond
  · rw [hPtop] at h
    exact Finset.mem_union.mpr (Or.inl
      ((GridPentagonBetween.mem_coveredSquares D.pentagon p).2 (Or.inr (Or.inl ⟨h.1, h.2⟩))))
  · rw [hPbottom] at h
    have hsplit : p.2 ∈ Grid.cIco D.pentagon.bottom s ∨
          p.2 ∈ Grid.cIco D.rectangle.bottom D.pentagon.bottom :=
      Finset.mem_union.mp
        (Grid.cIco_subset_cIco_union_cIco (t := D.rectangle.bottom)
          (w := D.pentagon.bottom) (u := s) h.2)
    rcases hsplit with hfirst | hsecond
    · exact Finset.mem_union.mpr (Or.inl
        ((GridPentagonBetween.mem_coveredSquares D.pentagon p).2 (Or.inr (Or.inr ⟨h.1, hfirst⟩))))
    · rw [D.pentagon_bottom_eq_rectangle_top hcommon] at hsecond
      have hcolumn : p.1 ∈ Grid.cIco D.rectangle.left D.rectangle.right := by
        have hmem : D.pentagon.right ∈ Grid.cIco D.rectangle.left D.rectangle.right :=
          Grid.cIoo_subset_cIco _ _ hcol
        simpa only [h.1, D.pentagon.right_eq] using hmem
      exact Finset.mem_union.mpr (Or.inr (hrect p hcolumn hsecond))

/-- The squares covered by the promoted pentagon of the common-initial-side overlap recut are
covered by the original pentagon or by the original rectangle. -/
theorem coveredSquares_pentagon_subset_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.coveredSquares ⊆
      D.pentagon.coveredSquares ∪ D.rectangle.toGridRectangle.coveredSquares := by
  intro p hp
  rcases D.isRecutOfLeftEqLeft_branch hone hrectangle hpentagon hcommon with
    ⟨hcol, hleft⟩ | ⟨hcol, hleft⟩
  · exact Finset.mem_union.mpr (Or.inl
      (D.mem_coveredSquares_pentagon_of_branch1 hcommon hone hrectangle hpentagon hcol hleft p hp))
  · exact D.mem_coveredSquares_pentagon_of_branch2 hcommon hone hrectangle hpentagon hcol hleft p hp

/-- The promoted pentagon of the common-initial-side overlap recut carries no `X`-marking as soon
as neither the original pentagon nor the original rectangle does. -/
theorem disjoint_coveredSquares_XSet_pentagon_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) (G : GridDiagram n)
    (hX : Disjoint D.pentagon.coveredSquares G.XSet)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet) :
    Disjoint (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.coveredSquares
      G.XSet :=
  (Finset.disjoint_union_left.mpr ⟨hX, hrectX⟩).mono_left
    (D.coveredSquares_pentagon_subset_recutLeftEqLeft hcommon hone hrectangle hpentagon)

end GridRectanglePentagonDecomposition

end TauCeti
