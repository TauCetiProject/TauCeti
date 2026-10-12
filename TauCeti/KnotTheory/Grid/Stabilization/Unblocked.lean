/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Rectangle
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

The grid states of `G'` split into those that contain `c`, denoted `I`, and the others, denoted
`N`. This file proves two coefficient-level facts about the unblocked differential `∂⁻` of
`G'`. They are the ingredients of the presentation of `GC⁻(G')` as the mapping cone of the
component `I → N` of `∂⁻` in `TauCeti.KnotTheory.Grid.Stabilization.Cone`, with the `I` block
identified with `GC⁻(G)` over one more variable; this is the form in which Ozsváth, Stipsicz and
Szabó compare the stabilized complex with `GC⁻(G)`.

* **The `N`-to-`I` coefficient block vanishes.** A rectangle from a state outside `I` to a state
  in `I` has `c` as a corner, so it covers one of the two `X`-marked squares of the block. Hence
  `∂⁻` has no matrix coefficient from `N` to `I` (`unblockedCoefficient_stabilizeX_eq_zero`).
* **The `I` coefficient block agrees with `GC⁻(G)` over one more variable.** Every state of `I`
  is obtained from a unique state of `G` by inserting `c` (`GridState.insertPoint`), and inserting
  `c` identifies the rectangles counted by `∂⁻` between states in `I` with those counted by
  `∂⁻` on `GC⁻(G)`. The two
  `X`-markings of the block cover exactly the squares that the `X`-marking of column `s` covers
  in `G`, and a rectangle avoiding them never covers `c` or the new `O`-marking. So the matrix
  coefficients agree after renaming the variables of `G` into those of `G'`; the variable of
  the new `O`-marking never occurs (`unblockedCoefficient_stabilizeX_insertPoint`).

## Main results

* `TauCeti.GridDiagram.unblockedCoefficient_stabilizeX_insertPoint`: the matrix coefficients of
  `∂⁻` between states containing `c` are the renamed coefficients of `∂⁻` for `G`.
* `TauCeti.GridDiagram.unblockedCoefficient_stabilizeX_eq_zero`: `∂⁻` has no matrix coefficient
  from a state not containing `c` to a state containing it.

## References

These coefficient identities are part of the stabilization-invariance argument in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2, where the complex of
the stabilized diagram is identified with a mapping cone built from the complex of `G`.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

open GridRectangleBetween

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
/-- If a transported rectangle avoids the split `X`-square, it covers the `O`-markings of the old
columns of the stabilization that the original rectangle covers in `G`, and never the new
`O`-marking. -/
@[simp]
theorem OColumns_stabilizeX_insertPoint {x y : GridState n} {R : GridRectangleBetween x y}
    (hXs : (s, G.X s) ∉ R.toGridRectangle.coveredSquares) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        (R.insertPoint s.succ (G.X s).succ).toGridRectangle =
      (G.OColumns R.toGridRectangle).map s.castSucc.succAboveEmb := by
  ext c
  simp only [mem_OColumns, Finset.mem_map, Fin.coe_succAboveEmb,
    mem_coveredSquares_insertPoint_succ_succ]
  induction c using Fin.succAboveCases s.castSucc with
  | x =>
    simp only [stabilizeX_O, GridState.insertPoint_apply_newColumn, Fin.predAbove_castSucc_self]
    simp only [hXs, false_iff, not_exists, not_and]
    exact fun c _ h => Fin.succAbove_ne _ _ h
  | p i =>
    simp only [stabilizeX_O, GridState.insertPoint_apply_succAbove, Fin.predAbove_succAbove]
    simp only [Fin.succAbove_right_inj, exists_eq_right]

variable (R : Type*) [CommSemiring R]

variable {s} in
/-- If a transported rectangle avoids the split `X`-square, its weight is the weight of the
original rectangle with the variables renamed into those of the stabilization. -/
@[simp]
theorem OMonomial_stabilizeX_insertPoint {x y : GridState n} {r : GridRectangleBetween x y}
    (hXs : (s, G.X s) ∉ r.toGridRectangle.coveredSquares) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).OMonomial R
        (r.insertPoint s.succ (G.X s).succ).toGridRectangle =
      rename s.castSucc.succAbove (G.OMonomial R r.toGridRectangle) := by
  rw [OMonomial_eq_monomial, OMonomial_eq_monomial, G.OColumns_stabilizeX_insertPoint hXs,
    rename_monomial, Finsupp.mapDomain_finsetSum, Finset.sum_map]
  simp [Finsupp.mapDomain_single]

variable {s} in
/-- Transporting along the insertion of the centre `c = (s.succ, (G.X s).succ)` identifies the
rectangles counted by the unblocked differential of `G` with those counted by the unblocked
differential of the stabilization between states containing `c`. -/
theorem mem_unblockedRectangles_stabilizeX_insertPoint {x y : GridState n}
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
    insertPoint_bottom, insertPoint_top, Grid.mem_cIoo_succ_succAbove_succ_succAbove_iff] at hc
  have hcov : (s, G.X s) ∈ r.toGridRectangle.coveredSquares := by
    simpa only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
      toGridRectangle_bottom, toGridRectangle_top] using hc
  exact Finset.disjoint_left.mp h.2 hcov ((G.mem_XSet _).mpr rfl)

/-- **The `I` coefficient block of the stabilized complex.** Between grid states containing the
centre `c = (s.succ, (G.X s).succ)` of the new block, the matrix coefficients of the unblocked
differential of the stabilization are those of `G`, with the variable of each column renamed to
the variable of the corresponding old column. The variable of the new `O`-marking does not
occur. -/
@[simp]
theorem unblockedCoefficient_stabilizeX_insertPoint (x y : GridState n) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedCoefficient R
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) =
      rename s.castSucc.succAbove (G.unblockedCoefficient R x y) := by
  rw [unblockedCoefficient_def, unblockedCoefficient_def, map_sum]
  symm
  refine Finset.sum_nbij (fun r => r.insertPoint s.succ (G.X s).succ)
    (fun r hr => (G.mem_unblockedRectangles_stabilizeX_insertPoint r).mpr hr)
    (fun r _ r' _ h => insertPoint_injective _ _ h) (fun r' hr' => ?_)
    (fun r hr => (G.OMonomial_stabilizeX_insertPoint R (fun h =>
      Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) h
        ((G.mem_XSet _).mpr rfl))).symm)
  obtain ⟨r, rfl⟩ := exists_insertPoint_eq r'
  exact ⟨r, (G.mem_unblockedRectangles_stabilizeX_insertPoint r).mp hr', rfl⟩

/-- **The `N`-to-`I` coefficient block vanishes.** The unblocked differential of the stabilization
has no matrix coefficient from a grid state not containing the centre
`c = (s.succ, (G.X s).succ)` of the new block to one containing it: such a rectangle has `c` as
a corner and covers one of the two `X`-marked squares of the block. -/
@[simp]
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
    simp
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
