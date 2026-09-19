/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Basic
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The unblocked complex of a stabilized grid

Let `G` be a grid diagram of size `n`, let `s` be a column, and let
`G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization that splits the
`X`-marking of column `s` by inserting a new column immediately before `s` and a new row
immediately below that marking. In `G'` the new `2 × 2` block is centred at the grid point
`c = (s.succ, (G.X s).succ)`: its two `X`-markings lie in the squares northwest and southeast
of `c`, the new `O`-marking in the square southwest of `c`, and the square northeast of `c` is
empty.

The grid states of `G'` split into those that contain `c`, spanning a submodule `I`, and the
others, spanning `N`. This file proves two facts about the unblocked differential `∂⁻` of `G'`.
Together they present `GC⁻(G')` as the mapping cone of the component `I → N` of `∂⁻`, with `I`
carrying the complex `GC⁻(G)` over one more variable; this is the form in which Ozsváth,
Stipsicz and Szabó compare the stabilized complex with `GC⁻(G)`.

* **`N` is a subcomplex.** A rectangle from a state outside `I` to a state in `I` has `c` as a
  corner, so it covers one of the two `X`-marked squares of the block. Hence `∂⁻` has no matrix
  coefficient from `N` to `I` (`unblockedCoefficient_stabilizeX_eq_zero`).
* **The quotient `I` is `GC⁻(G)` with one more variable.** Every state of `I` is obtained from a
  unique state of `G` by inserting `c` (`GridState.insertPoint`), and inserting `c` identifies
  the rectangles counted by `∂⁻` on `I` with those counted by `∂⁻` on `GC⁻(G)`. The two
  `X`-markings of the block cover exactly the squares that the `X`-marking of column `s` covers
  in `G`, and a rectangle avoiding them never covers `c` or the new `O`-marking. So the matrix
  coefficients agree after renaming the variables of `G` into those of `G'`; the variable of
  the new `O`-marking never occurs (`unblockedCoefficient_stabilizeX_insertPoint`).

The oriented rectangles are transported by `GridRectangleBetween.insertPoint`, which makes sense
for any inserted point. Their covered squares are compared through the collapse `Fin.predAbove`,
which sends both new lines back onto the old line they were inserted next to.

## Main definitions

* `TauCeti.GridRectangleBetween.insertPoint`: an oriented rectangle between two grid states,
  transported to the states obtained by inserting one point.

## Main results

* `TauCeti.GridRectangleBetween.exists_insertPoint_eq`: every rectangle between two states with
  a common inserted point is transported from the smaller grid.
* `TauCeti.GridRectangleBetween.isEmpty_insertPoint_iff`: a transported rectangle is empty
  exactly when the original one is and the inserted point is not in its interior.
* `TauCeti.GridDiagram.unblockedCoefficient_stabilizeX_insertPoint`: the matrix coefficients of
  `∂⁻` between states containing `c` are the renamed coefficients of `∂⁻` for `G`.
* `TauCeti.GridDiagram.unblockedCoefficient_stabilizeX_eq_zero`: `∂⁻` has no matrix coefficient
  from a state not containing `c` to a state containing it.

## References

This is the first step of the proof of stabilization invariance in Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Section 5.2, which identifies the complex of the stabilized
diagram with a mapping cone built from the complex of `G`.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- An oriented rectangle from `x` to `y`, transported to the states obtained from `x` and `y`
by inserting the point `(p, q)`. Its side columns are the embedded side columns. -/
def insertPoint (R : GridRectangleBetween x y) (p q : Fin (n + 1)) :
    GridRectangleBetween (x.insertPoint p q) (y.insertPoint p q) where
  left := p.succAbove R.left
  right := p.succAbove R.right
  left_ne_right := p.succAbove_right_injective.ne R.left_ne_right
  map_left := by simp [R.map_left]
  map_right := by simp [R.map_right]
  map_of_ne c := by
    induction c using Fin.succAboveCases p with
    | x => simp
    | p c =>
      intro hl hr
      simp only [GridState.insertPoint_apply_succAbove]
      rw [R.map_of_ne c (fun h => hl (h ▸ rfl)) fun h => hr (h ▸ rfl)]

variable (R : GridRectangleBetween x y) (p q : Fin (n + 1))

/-- The initial side of a transported rectangle is the embedded initial side. -/
@[simp]
theorem insertPoint_left : (R.insertPoint p q).left = p.succAbove R.left :=
  (rfl)

/-- The terminal side of a transported rectangle is the embedded terminal side. -/
@[simp]
theorem insertPoint_right : (R.insertPoint p q).right = p.succAbove R.right :=
  (rfl)

/-- The bottom row of a transported rectangle is the embedded bottom row. -/
@[simp]
theorem insertPoint_bottom : (R.insertPoint p q).bottom = q.succAbove R.bottom := by
  simp [bottom_def]

/-- The top row of a transported rectangle is the embedded top row. -/
@[simp]
theorem insertPoint_top : (R.insertPoint p q).top = q.succAbove R.top := by
  simp [top_def]

/-- Transporting rectangles along an inserted point is injective. -/
theorem insertPoint_injective :
    Function.Injective fun R : GridRectangleBetween x y => R.insertPoint p q := by
  intro R S h
  have hl := congrArg GridRectangleBetween.left h
  have hr := congrArg GridRectangleBetween.right h
  simp only [insertPoint_left, insertPoint_right] at hl hr
  exact sidePair_injective (Prod.ext (p.succAbove_right_injective hl)
    (p.succAbove_right_injective hr))

variable {p q} in
/-- Every rectangle between two states containing the same inserted point is transported from a
rectangle of the smaller grid. The inserted column is not a side column, since both states use
the inserted row there. -/
theorem exists_insertPoint_eq
    (S : GridRectangleBetween (x.insertPoint p q) (y.insertPoint p q)) :
    ∃ R : GridRectangleBetween x y, R.insertPoint p q = S := by
  have hleft : S.left ≠ p := by
    intro h
    obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (h ▸ S.left_ne_right.symm)
    have hmap := S.map_left
    rw [h, GridState.insertPoint_apply_newColumn, ← hr,
      GridState.insertPoint_apply_succAbove] at hmap
    exact q.succAbove_ne _ hmap.symm
  have hright : S.right ≠ p := by
    intro h
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (h ▸ S.left_ne_right)
    have hmap := S.map_right
    rw [h, GridState.insertPoint_apply_newColumn, ← hl,
      GridState.insertPoint_apply_succAbove] at hmap
    exact q.succAbove_ne _ hmap.symm
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hleft
  obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hright
  refine ⟨⟨l, r, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro rfl
    exact S.left_ne_right (hl.symm.trans hr)
  · apply q.succAbove_right_injective
    simpa [← hl, ← hr] using S.map_left
  · apply q.succAbove_right_injective
    simpa [← hl, ← hr] using S.map_right
  · intro c hcl hcr
    apply q.succAbove_right_injective
    simpa using S.map_of_ne (p.succAbove c) (hl ▸ p.succAbove_right_injective.ne hcl)
      (hr ▸ p.succAbove_right_injective.ne hcr)
  · exact sidePair_injective (Prod.ext hl hr)

/-- A transported rectangle covers the embedded image of a square exactly when the original
rectangle covers that square. -/
theorem succAbove_mem_coveredSquares_insertPoint (c r : Fin n) :
    (p.succAbove c, q.succAbove r) ∈ (R.insertPoint p q).toGridRectangle.coveredSquares ↔
      (c, r) ∈ R.toGridRectangle.coveredSquares := by
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, insertPoint_left, insertPoint_right,
    insertPoint_bottom, insertPoint_top, Grid.succAbove_mem_cIco_succAbove_succAbove]

/-- When the point is inserted immediately after the column `i` and the row `j`, a square of
the larger grid is covered by a transported rectangle exactly when its collapse under
`Fin.predAbove` is covered by the original rectangle. -/
theorem mem_coveredSquares_insertPoint_succ_succ (i j : Fin n) (a : Fin (n + 1) × Fin (n + 1)) :
    a ∈ (R.insertPoint i.succ j.succ).toGridRectangle.coveredSquares ↔
      (i.predAbove a.1, j.predAbove a.2) ∈ R.toGridRectangle.coveredSquares := by
  simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, insertPoint_left, insertPoint_right,
    insertPoint_bottom, insertPoint_top, Grid.mem_cIco_succ_succAbove_succ_succAbove_iff]

/-- A transported rectangle is empty exactly when the original rectangle is empty and the
inserted point does not lie in the interior of the transported rectangle. -/
theorem isEmpty_insertPoint_iff :
    (R.insertPoint p q).IsEmpty ↔
      R.IsEmpty ∧ (p, q) ∉ (R.insertPoint p q).toGridRectangle.interior := by
  rw [isEmpty_iff_forall_notMem_cIoo, isEmpty_iff_forall_notMem_cIoo,
    Fin.forall_iff_succAbove p, and_comm]
  simp only [GridRectangle.mem_interior, GridRectangle.mem_columnInterior,
    GridRectangle.mem_rowInterior, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, insertPoint_left, insertPoint_right,
    insertPoint_bottom, insertPoint_top, GridState.insertPoint_apply_newColumn,
    GridState.insertPoint_apply_succAbove, Grid.succAbove_mem_cIoo_succAbove_succAbove, not_and]

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

open GridRectangleBetween

/-- In the stabilization splitting the `X`-marking of column `s`, the `X`-marking of each column
collapses under `Fin.predAbove` onto the `X`-marking of `G` in the collapsed column: both
`X`-markings of the new block collapse onto the split marking. -/
theorem predAbove_X_stabilizeX (c : Fin (n + 1)) :
    (G.X s).predAbove ((G.stabilizeX s.castSucc (G.X s).castSucc s).X c) =
      G.X (s.predAbove c) := by
  induction c using Fin.succAboveCases s.castSucc with
  | x => simp
  | p i =>
    rw [stabilizeX_X, GridState.splitPoint_apply_succAbove, Fin.predAbove_succAbove]
    split_ifs with h
    · simp [h]
    · exact Fin.predAbove_succAbove _ _

/-- The `O`-marking of each old column of the stabilization collapses under `Fin.predAbove`
onto the `O`-marking of the corresponding column of `G`. -/
theorem predAbove_O_stabilizeX_succAbove (i : Fin n) :
    (G.X s).predAbove
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).O (s.castSucc.succAbove i)) =
      G.O i := by
  simp

/-- The new `O`-marking of the stabilization lies in the new column and collapses onto the
row of the split `X`-marking. -/
theorem predAbove_O_stabilizeX_castSucc :
    (G.X s).predAbove ((G.stabilizeX s.castSucc (G.X s).castSucc s).O s.castSucc) = G.X s := by
  simp

variable {s} in
/-- A rectangle between states containing the centre `c = (s.succ, (G.X s).succ)` of the new
block avoids the `X`-markings of the stabilization exactly when the rectangle it is transported
from avoids the `X`-markings of `G`. -/
theorem disjoint_XSet_stabilizeX_insertPoint {x y : GridState n} (R : GridRectangleBetween x y) :
    Disjoint (R.insertPoint s.succ (G.X s).succ).toGridRectangle.coveredSquares
        (G.stabilizeX s.castSucc (G.X s).castSucc s).XSet ↔
      Disjoint R.toGridRectangle.coveredSquares G.XSet := by
  simp only [Finset.disjoint_right, Prod.forall, mem_XSet]
  constructor
  · rintro h c _ rfl hc
    obtain ⟨c', rfl⟩ := Fin.predAbove_surjective s c
    refine h c' _ rfl ?_
    rw [mem_coveredSquares_insertPoint_succ_succ, predAbove_X_stabilizeX]
    exact hc
  · rintro h c' _ rfl hc
    rw [mem_coveredSquares_insertPoint_succ_succ, predAbove_X_stabilizeX] at hc
    exact h _ _ rfl hc

variable {s} in
/-- A transported rectangle avoiding the `X`-markings covers the `O`-markings of the old
columns of the stabilization that the original rectangle covers in `G`, and never the new
`O`-marking. -/
theorem OColumns_stabilizeX_insertPoint {x y : GridState n} {R : GridRectangleBetween x y}
    (hR : Disjoint R.toGridRectangle.coveredSquares G.XSet) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        (R.insertPoint s.succ (G.X s).succ).toGridRectangle =
      (G.OColumns R.toGridRectangle).map s.castSucc.succAboveEmb := by
  ext c
  simp only [mem_OColumns, Finset.mem_map, Fin.coe_succAboveEmb,
    mem_coveredSquares_insertPoint_succ_succ]
  induction c using Fin.succAboveCases s.castSucc with
  | x =>
    rw [predAbove_O_stabilizeX_castSucc, Fin.predAbove_castSucc_self]
    have hXs : (s, G.X s) ∉ R.toGridRectangle.coveredSquares :=
      fun h => Finset.disjoint_left.mp hR h ((G.mem_XSet _).mpr rfl)
    simp only [hXs, false_iff, not_exists, not_and]
    exact fun c _ h => Fin.succAbove_ne _ _ h
  | p i =>
    rw [predAbove_O_stabilizeX_succAbove, Fin.predAbove_succAbove]
    simp only [Fin.succAbove_right_inj, exists_eq_right]

variable (R : Type*) [CommSemiring R]

variable {s} in
/-- The weight of a transported rectangle avoiding the `X`-markings is the weight of the
original rectangle with the variables renamed into those of the stabilization. -/
theorem OMonomial_stabilizeX_insertPoint {x y : GridState n} {r : GridRectangleBetween x y}
    (hr : Disjoint r.toGridRectangle.coveredSquares G.XSet) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OMonomial R
        (r.insertPoint s.succ (G.X s).succ).toGridRectangle =
      rename s.castSucc.succAbove (G.OMonomial R r.toGridRectangle) := by
  rw [OMonomial_eq_monomial, OMonomial_eq_monomial, G.OColumns_stabilizeX_insertPoint hr,
    rename_monomial, Finsupp.mapDomain_finsetSum, Finset.sum_map]
  simp [Finsupp.mapDomain_single]

variable {s} in
/-- Transporting along the insertion of the centre `c = (s.succ, (G.X s).succ)` identifies the
rectangles counted by the unblocked differential of `G` with those counted by the unblocked
differential of the stabilization between states containing `c`. -/
theorem insertPoint_mem_unblockedRectangles_stabilizeX_iff {x y : GridState n}
    (r : GridRectangleBetween x y) :
    r.insertPoint s.succ (G.X s).succ ∈
        (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedRectangles
          (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) ↔
      r ∈ G.unblockedRectangles x y := by
  rw [mem_unblockedRectangles, mem_unblockedRectangles, disjoint_XSet_stabilizeX_insertPoint,
    isEmpty_insertPoint_iff]
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun hc => ?_⟩, h.2⟩⟩
  -- The centre lies inside the transported rectangle only if the original rectangle covers the
  -- `X`-marked square of the split column.
  simp only [GridRectangle.mem_interior, GridRectangle.mem_columnInterior,
    GridRectangle.mem_rowInterior, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, insertPoint_left, insertPoint_right,
    insertPoint_bottom, insertPoint_top, Grid.succ_mem_cIoo_succAbove_succAbove_iff] at hc
  have hcov : (s, G.X s) ∈ r.toGridRectangle.coveredSquares := by
    simpa only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
      toGridRectangle_bottom, toGridRectangle_top] using hc
  exact Finset.disjoint_left.mp h.2 hcov ((G.mem_XSet _).mpr rfl)

/-- **The quotient `I` of the stabilized complex.** Between grid states containing the centre
`c = (s.succ, (G.X s).succ)` of the new block, the matrix coefficients of the unblocked
differential of the stabilization are those of `G`, with the variable of each column renamed to
the variable of the corresponding old column. The variable of the new `O`-marking does not
occur. -/
theorem unblockedCoefficient_stabilizeX_insertPoint (x y : GridState n) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedCoefficient R
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) =
      rename s.castSucc.succAbove (G.unblockedCoefficient R x y) := by
  rw [unblockedCoefficient_def, unblockedCoefficient_def, map_sum]
  symm
  refine Finset.sum_nbij (fun r => r.insertPoint s.succ (G.X s).succ)
    (fun r hr => (G.insertPoint_mem_unblockedRectangles_stabilizeX_iff r).mpr hr)
    (fun r _ r' _ h => insertPoint_injective _ _ h) (fun r' hr' => ?_)
    (fun r hr => (G.OMonomial_stabilizeX_insertPoint R
      (G.disjoint_XSet_of_mem_unblockedRectangles hr)).symm)
  obtain ⟨r, rfl⟩ := exists_insertPoint_eq r'
  exact ⟨r, (G.insertPoint_mem_unblockedRectangles_stabilizeX_iff r).mp hr', rfl⟩

/-- **`N` is a subcomplex of the stabilized complex.** The unblocked differential of the
stabilization has no matrix coefficient from a grid state not containing the centre
`c = (s.succ, (G.X s).succ)` of the new block to one containing it: such a rectangle has `c` as
a corner and covers one of the two `X`-marked squares of the block. -/
theorem unblockedCoefficient_stabilizeX_eq_zero {y z : GridState (n + 1)}
    (hy : y s.succ ≠ (G.X s).succ) (hz : z s.succ = (G.X s).succ) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedCoefficient R y z = 0 := by
  rw [unblockedCoefficient_def]
  refine Finset.sum_eq_zero fun r hr => absurd hr fun hr => ?_
  have hX := (G.stabilizeX s.castSucc (G.X s).castSucc s).disjoint_XSet_of_mem_unblockedRectangles
    hr
  have hbt : r.bottom ≠ r.top := fun h => r.left_ne_right (y.toPerm.injective h)
  by_cases hl : s.succ = r.left
  · -- `c` is the northwest corner, and `r` covers the `X`-marked square southeast of `c`.
    have htop : r.top = (G.X s).succ := by rw [top_def, ← r.map_left, ← hl, hz]
    have hcov : (s.succ, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares := by
      simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
        GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
        toGridRectangle_bottom, toGridRectangle_top]
      rw [← hl, htop]
      exact ⟨hl ▸ Grid.left_mem_cIco r.left_ne_right,
        Grid.castSucc_mem_cIco_succ fun h => hbt (h.trans htop.symm)⟩
    refine Finset.disjoint_left.mp hX hcov ((mem_XSet _ _).mpr ?_)
    simpa using GridState.splitPoint_apply_splitColumn G.X s.castSucc (G.X s).castSucc s
  by_cases hr' : s.succ = r.right
  · -- `c` is the southeast corner, and `r` covers the `X`-marked square northwest of `c`.
    have hbot : r.bottom = (G.X s).succ := by rw [bottom_def, ← r.map_right, ← hr', hz]
    have hcov : (s.castSucc, (G.X s).succ) ∈ r.toGridRectangle.coveredSquares := by
      simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
        GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
        toGridRectangle_bottom, toGridRectangle_top]
      rw [← hr', hbot]
      exact ⟨Grid.castSucc_mem_cIco_succ fun h => r.left_ne_right (h.trans hr'),
        hbot ▸ Grid.left_mem_cIco hbt⟩
    refine Finset.disjoint_left.mp hX hcov ((mem_XSet _ _).mpr ?_)
    simp
  -- Otherwise the two states agree in the column of `c`.
  exact hy ((r.map_of_ne s.succ hl hr').symm.trans hz)

end GridDiagram

end TauCeti
