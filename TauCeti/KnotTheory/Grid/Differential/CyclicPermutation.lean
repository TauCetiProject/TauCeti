/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Relabeling
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The grid differentials under cyclic permutation

A grid diagram lives on a torus, so cyclically permuting its rows or its columns does not change
the diagram it draws; these are the cyclic permutation moves `GridDiagram.IsMove.cyclicRows` and
`GridDiagram.IsMove.cyclicColumns`. This file shows that the grid differentials see no difference
either: relabeling every grid state by the same cyclic permutation identifies the rectangles
counted by the differential of `G` with those counted by the differential of the permuted
diagram, together with their weights.

For a cyclic permutation of the rows the variables `V_c` of the unblocked complex, which are
indexed by columns, are untouched, and the chain relabeling `GridChain.relabelRowsEquiv` is a
linear isomorphism intertwining the two unblocked differentials. For a cyclic permutation of the
columns the rectangle weights are renamed by the same permutation, so the intertwining map on
`GC⁻` also renames the variables in the coefficients. The fully blocked complex has no variables,
so there the chain relabelings intertwine the differentials for rows and columns alike.

## Main results

* `TauCeti.GridDiagram.unblockedCoefficient_relabelRows_finRotate`,
  `TauCeti.GridDiagram.unblockedCoefficient_relabelColumns_finRotate`: the matrix coefficients of
  the unblocked differential of a cyclically permuted diagram.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_relabelRows_finRotate`,
  `TauCeti.GridDiagram.fullyBlockedRectangleCount_relabelColumns_finRotate`: the fully blocked
  rectangle counts are invariant.
* `TauCeti.GridDiagram.unblockedDifferential_relabelRows_finRotate`: the row relabeling
  intertwines the unblocked differentials.
* `TauCeti.GridDiagram.unblockedDifferential_relabelColumns_finRotate`: the column relabeling,
  followed by renaming the variables, intertwines the unblocked differentials.
* `TauCeti.GridDiagram.fullyBlockedDifferential_relabelRows_finRotate`,
  `TauCeti.GridDiagram.fullyBlockedDifferential_relabelColumns_finRotate`: the chain relabelings
  intertwine the fully blocked differentials.

## References

The invariance of the grid complexes under cyclic permutation follows Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapters 3--5.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

open GridRectangleBetween

/-! ### Cyclic permutation of the rows -/

/-- A cyclic permutation of the rows preserves and reflects `X`-avoidance of a rectangle. -/
theorem disjoint_XSet_relabelRows_finRotate {x y : GridState n} (r : GridRectangleBetween x y) :
    Disjoint (relabelRowsEquiv (finRotate n) x y r).toGridRectangle.coveredSquares
        (G.relabelRows (finRotate n)).XSet ↔
      Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  simp only [Finset.disjoint_left, Prod.forall, mem_coveredSquares_relabelRowsEquiv_finRotate,
    mem_XSet_relabelRows]
  exact forall_congr' fun c => (finRotate n).symm.forall_congr_right
    (q := fun b => (c, b) ∈ r.toGridRectangle.coveredSquares → (c, b) ∉ G.XSet)

/-- A cyclic permutation of the rows identifies the rectangles counted by the unblocked
differentials. -/
theorem mem_unblockedRectangles_relabelRows_finRotate {x y : GridState n}
    (r : GridRectangleBetween x y) :
    relabelRowsEquiv (finRotate n) x y r ∈
        (G.relabelRows (finRotate n)).unblockedRectangles (x.relabelRows (finRotate n))
          (y.relabelRows (finRotate n)) ↔
      r ∈ G.unblockedRectangles x y := by
  simp only [mem_unblockedRectangles, isEmpty_relabelRowsEquiv_finRotate,
    disjoint_XSet_relabelRows_finRotate]

/-- A cyclic permutation of the rows does not change which `O`-columns a rectangle covers. -/
@[simp]
theorem OColumns_relabelRows_finRotate {x y : GridState n} (r : GridRectangleBetween x y) :
    (G.relabelRows (finRotate n)).OColumns
        (relabelRowsEquiv (finRotate n) x y r).toGridRectangle =
      G.OColumns r.toGridRectangle := by
  ext c
  simp only [mem_OColumns, mem_coveredSquares_relabelRowsEquiv_finRotate, relabelRows_O_apply,
    Equiv.symm_apply_apply]

variable (R : Type*) [CommSemiring R]

/-- A cyclic permutation of the rows leaves the weight of a rectangle unchanged. -/
@[simp]
theorem OMonomial_relabelRows_finRotate {x y : GridState n} (r : GridRectangleBetween x y) :
    (G.relabelRows (finRotate n)).OMonomial R
        (relabelRowsEquiv (finRotate n) x y r).toGridRectangle =
      G.OMonomial R r.toGridRectangle := by
  rw [OMonomial_eq_monomial, OMonomial_eq_monomial, OColumns_relabelRows_finRotate]

/-- A cyclic permutation of the rows leaves the matrix coefficients of the unblocked differential
unchanged. -/
@[simp]
theorem unblockedCoefficient_relabelRows_finRotate (x y : GridState n) :
    (G.relabelRows (finRotate n)).unblockedCoefficient R (x.relabelRows (finRotate n))
        (y.relabelRows (finRotate n)) =
      G.unblockedCoefficient R x y := by
  rw [unblockedCoefficient_def, unblockedCoefficient_def]
  refine (Finset.sum_equiv (relabelRowsEquiv (finRotate n) x y)
    (fun r => (G.mem_unblockedRectangles_relabelRows_finRotate r).symm) fun r _ => ?_).symm
  rw [OMonomial_relabelRows_finRotate]

/-- A cyclic permutation of the rows leaves the fully blocked rectangle counts unchanged. -/
@[simp]
theorem fullyBlockedRectangleCount_relabelRows_finRotate (x y : GridState n) :
    (G.relabelRows (finRotate n)).fullyBlockedRectangleCount (x.relabelRows (finRotate n))
        (y.relabelRows (finRotate n)) =
      G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_eq_constantCoeff, fullyBlockedRectangleCount_eq_constantCoeff,
    unblockedCoefficient_relabelRows_finRotate]

/-- The chain relabeling by a cyclic permutation of the rows intertwines the unblocked
differentials of `G` and of the row-permuted diagram. -/
theorem unblockedDifferential_relabelRows_finRotate :
    (G.relabelRows (finRotate n)).unblockedDifferential R ∘ₗ
        (GridChain.relabelRowsEquiv (finRotate n)).toLinearMap =
      (GridChain.relabelRowsEquiv (finRotate n)).toLinearMap ∘ₗ G.unblockedDifferential R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelRows (finRotate n) = y :=
    ⟨y.relabelRows (finRotate n).symm, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    GridChain.relabelRowsEquiv_single, unblockedDifferential_single_apply,
    GridChain.relabelRowsEquiv_apply, GridState.relabelRows_relabelRows, Equiv.self_trans_symm,
    GridState.relabelRows_refl, unblockedCoefficient_relabelRows_finRotate]

/-- The chain relabeling by a cyclic permutation of the rows intertwines the fully blocked
differentials of `G` and of the row-permuted diagram. -/
theorem fullyBlockedDifferential_relabelRows_finRotate :
    (G.relabelRows (finRotate n)).fullyBlockedDifferential ∘ₗ
        (GridChain.relabelRowsEquiv (finRotate n)).toLinearMap =
      (GridChain.relabelRowsEquiv (finRotate n)).toLinearMap ∘ₗ G.fullyBlockedDifferential := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelRows (finRotate n) = y :=
    ⟨y.relabelRows (finRotate n).symm, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    GridChain.relabelRowsEquiv_single, fullyBlockedDifferential_single_apply,
    GridChain.relabelRowsEquiv_apply, GridState.relabelRows_relabelRows, Equiv.self_trans_symm,
    GridState.relabelRows_refl, fullyBlockedRectangleCount_relabelRows_finRotate]

/-! ### Cyclic permutation of the columns -/

omit R in
/-- A cyclic permutation of the columns preserves and reflects `X`-avoidance of a rectangle. -/
theorem disjoint_XSet_relabelColumns_finRotate {x y : GridState n}
    (r : GridRectangleBetween x y) :
    Disjoint (relabelColumnsEquiv (finRotate n) x y r).toGridRectangle.coveredSquares
        (G.relabelColumns (finRotate n)).XSet ↔
      Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  simp only [Finset.disjoint_left, Prod.forall,
    mem_coveredSquares_relabelColumnsEquiv_finRotate, mem_XSet_relabelColumns]
  exact (finRotate n).symm.forall_congr_right
    (q := fun a => ∀ b, (a, b) ∈ r.toGridRectangle.coveredSquares → (a, b) ∉ G.XSet)

omit R in
/-- A cyclic permutation of the columns identifies the rectangles counted by the unblocked
differentials. -/
theorem mem_unblockedRectangles_relabelColumns_finRotate {x y : GridState n}
    (r : GridRectangleBetween x y) :
    relabelColumnsEquiv (finRotate n) x y r ∈
        (G.relabelColumns (finRotate n)).unblockedRectangles (x.relabelColumns (finRotate n))
          (y.relabelColumns (finRotate n)) ↔
      r ∈ G.unblockedRectangles x y := by
  simp only [mem_unblockedRectangles, isEmpty_relabelColumnsEquiv_finRotate,
    disjoint_XSet_relabelColumns_finRotate]

omit R in
/-- A cyclic permutation of the columns renames the `O`-columns a rectangle covers. -/
@[simp]
theorem OColumns_relabelColumns_finRotate {x y : GridState n} (r : GridRectangleBetween x y) :
    (G.relabelColumns (finRotate n)).OColumns
        (relabelColumnsEquiv (finRotate n) x y r).toGridRectangle =
      (G.OColumns r.toGridRectangle).map (finRotate n).toEmbedding := by
  ext c
  obtain ⟨c, rfl⟩ := (finRotate n).surjective c
  simp only [mem_OColumns, mem_coveredSquares_relabelColumnsEquiv_finRotate,
    relabelColumns_O_apply, Equiv.symm_apply_apply, Finset.mem_map_equiv]

/-- A cyclic permutation of the columns renames the variables in the weight of a rectangle. -/
@[simp]
theorem OMonomial_relabelColumns_finRotate {x y : GridState n} (r : GridRectangleBetween x y) :
    (G.relabelColumns (finRotate n)).OMonomial R
        (relabelColumnsEquiv (finRotate n) x y r).toGridRectangle =
      rename (finRotate n) (G.OMonomial R r.toGridRectangle) := by
  rw [OMonomial_eq_monomial, OMonomial_eq_monomial, OColumns_relabelColumns_finRotate,
    rename_monomial, Finset.sum_map, Finsupp.mapDomain_finsetSum]
  simp only [Equiv.coe_toEmbedding, Finsupp.mapDomain_single]

/-- A cyclic permutation of the columns renames the variables in the matrix coefficients of the
unblocked differential. -/
@[simp]
theorem unblockedCoefficient_relabelColumns_finRotate (x y : GridState n) :
    (G.relabelColumns (finRotate n)).unblockedCoefficient R (x.relabelColumns (finRotate n))
        (y.relabelColumns (finRotate n)) =
      rename (finRotate n) (G.unblockedCoefficient R x y) := by
  rw [unblockedCoefficient_def, unblockedCoefficient_def, map_sum]
  refine (Finset.sum_equiv (relabelColumnsEquiv (finRotate n) x y)
    (fun r => (G.mem_unblockedRectangles_relabelColumns_finRotate r).symm) fun r _ => ?_).symm
  rw [OMonomial_relabelColumns_finRotate]

omit R in
/-- A cyclic permutation of the columns leaves the fully blocked rectangle counts unchanged. -/
@[simp]
theorem fullyBlockedRectangleCount_relabelColumns_finRotate (x y : GridState n) :
    (G.relabelColumns (finRotate n)).fullyBlockedRectangleCount
        (x.relabelColumns (finRotate n)) (y.relabelColumns (finRotate n)) =
      G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_eq_constantCoeff, fullyBlockedRectangleCount_eq_constantCoeff,
    unblockedCoefficient_relabelColumns_finRotate, constantCoeff_rename]

/-- The chain relabeling by a cyclic permutation of the columns, which also renames the variables
of the coefficients by the same permutation, intertwines the unblocked differentials of `G` and of
the column-permuted diagram. -/
theorem unblockedDifferential_relabelColumns_finRotate :
    ((G.relabelColumns (finRotate n)).unblockedDifferential R).comp
        (GridChain.relabelColumnsRenameEquiv R (finRotate n)).toLinearMap =
      (GridChain.relabelColumnsRenameEquiv R (finRotate n)).toLinearMap.comp
        (G.unblockedDifferential R) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelColumns (finRotate n) = y :=
    ⟨y.relabelColumns (finRotate n).symm, by simp⟩
  simp only [GridChain.relabelColumnsRenameEquiv_toLinearMap, LinearMap.comp_apply,
    Finsupp.lsingle_apply, GridChain.relabelColumnsRename_single, map_one,
    unblockedDifferential_single_apply, GridChain.relabelColumnsRename_apply,
    GridState.relabelColumns_relabelColumns, Equiv.self_trans_symm, GridState.relabelColumns_refl,
    unblockedCoefficient_relabelColumns_finRotate]

/-- The chain relabeling by a cyclic permutation of the columns intertwines the fully blocked
differentials of `G` and of the column-permuted diagram. -/
theorem fullyBlockedDifferential_relabelColumns_finRotate :
    (G.relabelColumns (finRotate n)).fullyBlockedDifferential ∘ₗ
        (GridChain.relabelColumnsEquiv (finRotate n)).toLinearMap =
      (GridChain.relabelColumnsEquiv (finRotate n)).toLinearMap ∘ₗ
        G.fullyBlockedDifferential := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelColumns (finRotate n) = y :=
    ⟨y.relabelColumns (finRotate n).symm, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    GridChain.relabelColumnsEquiv_single, fullyBlockedDifferential_single_apply,
    GridChain.relabelColumnsEquiv_apply, GridState.relabelColumns_relabelColumns,
    Equiv.self_trans_symm, GridState.relabelColumns_refl,
    fullyBlockedRectangleCount_relabelColumns_finRotate]

end GridDiagram

end TauCeti
