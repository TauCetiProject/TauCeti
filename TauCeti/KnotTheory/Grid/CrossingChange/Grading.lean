/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Basic
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Basic

/-!
# The bidegrees of the crossing change maps

Exchanging two cyclically adjacent columns `a` and `b = finRotate n a` of a grid diagram `G` whose
marking segments interleave is a cross-commutation: `G` and `G' = G.swapColumns a b` present links
that differ by a crossing change. The pentagon-counting commutation map
`GridDiagram.commutationMap` of a column turn at these columns is a chain map `GC⁻(G) → GC⁻(G')`
at every turn row (`GridDiagram.commutationMap_comp_unblockedDifferential`), whether or not the
segments interleave. Its bidegree `GridDiagram.commutationBidegree` depends on the turn row. This
file finds the turn rows at which it has the bidegrees of the crossing change maps.

For interleaving segments, exactly one of the two `O`-markings lies on the open arc of the other
column (`GridDiagram.ColumnsInterleaving.O_mem_columnArc_iff`). Going up around the vertical
circle, the markings appear in one of two orders.

* If `O_a` lies on the arc of column `b`, the order is `O_b, O_a, X_b, X_a`. The commutation map
  turning in the row of `O_a` then has bidegree `(0, 0)`
  (`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc`).
* Otherwise the order is `O_b, X_a, X_b, O_a`. The commutation map turning in the row of `X_a`
  then has bidegree `(-2, -1)`, that of multiplication by `U`
  (`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`).

A cross-commutation exchanges the two orders
(`GridDiagram.ColumnsInterleaving.O_swapColumns_mem_columnArc_iff`). So of two diagrams related by
a cross-commutation, one has a chain map to the other preserving the bigrading, and the other has a
chain map back of bidegree `(-2, -1)`. These are the bidegrees of
the crossing change maps of Ozsváth--Stipsicz--Szabó, Section 6.1, whose two composites are chain
homotopic to multiplication by `U`. No such homotopy is constructed here. For knot grids the maps
induced on `GH⁻` are `R[U]`-linear and homogeneous of Alexander degrees `0` and `-1`
(`GridDiagram.IsKnot.isHomogeneous_unblockedHomologyCommutationLinearMap_of_mem_columnArc` and
`GridDiagram.IsKnot.isHomogeneous_unblockedHomologyCommutationLinearMap_of_notMem_columnArc`).
This is the shape of the maps in the comparison lemma
`GridDiagram.IsKnot.tau_le_tau_sub_of_comp_eq_X_pow_smul`, which turns them into a bound on the
change of `τ` across a crossing change once the composites are known.

## Main results

* `TauCeti.GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc` and
  `TauCeti.GridDiagram.commutationBidegree_eq_of_notMem_columnArc`: turn rows at which the
  commutation map of a cross-commutation has bidegree `(0, 0)`, respectively `(-2, -1)`.
* `isHomogeneous_unblockedHomologyCommutationLinearMap_of_mem_columnArc` and
  `isHomogeneous_unblockedHomologyCommutationLinearMap_of_notMem_columnArc`, in the namespace
  `TauCeti.GridDiagram.IsKnot`: the induced `R[U]`-linear maps on `GH⁻` of a knot grid are
  homogeneous of Alexander degrees `0` and `-1`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1: the crossing change maps and their gradings.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing change inequality for `τ` from grid diagrams.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} {G : GridDiagram n}

variable (C : ColumnTurn n)

/-- **A grading-preserving chain map across a crossing change.** If the segments of the two
columns of the column turn `C` interleave and the `O`-marking of the first column lies on the arc
of the second, then the commutation map turning in the row of that `O`-marking has bidegree
`(0, 0)`. -/
theorem commutationBidegree_eq_zero_of_mem_columnArc
    (h : G.ColumnsInterleaving C.column (finRotate n C.column))
    (hO : G.O C.column ∈ G.columnArc (finRotate n C.column)) (hs : C.turnRow = G.O C.column) :
    G.commutationBidegree C = 0 := by
  have hX :
      G.X C.column ∈ Grid.cIoo (G.X (finRotate n C.column)) (G.O (finRotate n C.column)) := by
    rcases (columnsInterleaving_iff G _ _).mp h with ⟨-, h₂⟩ | ⟨h₁, -⟩
    · exact h₂
    · exact absurd h₁ (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hO)
  have hO' : C.turnRow ∉ Grid.cIoo (G.O (finRotate n C.column)) (G.O C.column) := by
    rw [hs]
    exact Grid.right_notMem_cIoo _ _
  -- The row of `O_a` lies between `O_b` and `X_b`, so not between `X_b` and `X_a`, an arc inside
  -- the one from `X_b` up to `O_b`.
  have hX' : C.turnRow ∉ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) := by
    rw [hs]
    intro h₃
    exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hO
      (Grid.cIoo_subset_cIoo_right_of_mem_cIoo hX h₃)
  ext <;> simp only [commutationBidegree_fst, commutationBidegree_snd, hO', hX', ite_false,
    sub_zero, Prod.fst_zero, Prod.snd_zero]

/-- **A chain map of bidegree `(-2, -1)` across a crossing change.** If the segments of the two
columns of the column turn `C` interleave and the `O`-marking of the first column does not lie on
the arc of the second, then the commutation map turning in the row of the `X`-marking of the
first column has bidegree `(-2, -1)`, the bidegree of multiplication by `U`. -/
theorem commutationBidegree_eq_of_notMem_columnArc
    (h : G.ColumnsInterleaving C.column (finRotate n C.column))
    (hO : G.O C.column ∉ G.columnArc (finRotate n C.column)) (hs : C.turnRow = G.X C.column) :
    G.commutationBidegree C = (-2, -1) := by
  obtain ⟨h₁, h₂⟩ : G.O C.column ∈
      Grid.cIoo (G.X (finRotate n C.column)) (G.O (finRotate n C.column)) ∧
      G.X C.column ∈ G.columnArc (finRotate n C.column) := by
    rcases (columnsInterleaving_iff G _ _).mp h with ⟨h₁, -⟩ | h'
    · exact absurd h₁ hO
    · exact h'
  -- The row of `X_a` lies between `O_b` and `X_b`, an arc inside the one from `O_b` up to `O_a`.
  have hO' : C.turnRow ∈ Grid.cIoo (G.O (finRotate n C.column)) (G.O C.column) := by
    rw [hs]
    exact Grid.cIoo_subset_cIoo_right_of_mem_cIoo (Grid.mem_cIoo_cyclic_right h₁) h₂
  have hX' : C.turnRow ∉ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) := by
    rw [hs]
    exact Grid.right_notMem_cIoo _ _
  ext <;> simp only [commutationBidegree_fst, commutationBidegree_snd, hO', hX', ite_true,
    ite_false, zero_sub]

namespace IsKnot

variable (hG : G.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

/-- For a knot grid, the chain map of `GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc`
induces an `R[U]`-linear map on `GH⁻` that preserves the Alexander grading. -/
theorem isHomogeneous_unblockedHomologyCommutationLinearMap_of_mem_columnArc
    (h : G.ColumnsInterleaving C.column (finRotate n C.column))
    (hO : G.O C.column ∈ G.columnArc (finRotate n C.column)) (hs : C.turnRow = G.O C.column) :
    letI := hG.unblockedHomologyModule R
    letI := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule R
    LinearMap.IsHomogeneous (hG.unblockedHomologyCommutationLinearMap R C)
      (hG.alexanderUnblockedHomologyGrading R).piece
      ((hG.swapColumns C.column (finRotate n C.column)).alexanderUnblockedHomologyGrading R).piece
      0 := by
  simpa [commutationBidegree_eq_zero_of_mem_columnArc C h hO hs] using
    hG.isHomogeneous_unblockedHomologyCommutationLinearMap R C

/-- For a knot grid, the chain map of `GridDiagram.commutationBidegree_eq_of_notMem_columnArc`
induces an `R[U]`-linear map on `GH⁻` that lowers the Alexander grading by one. -/
theorem isHomogeneous_unblockedHomologyCommutationLinearMap_of_notMem_columnArc
    (h : G.ColumnsInterleaving C.column (finRotate n C.column))
    (hO : G.O C.column ∉ G.columnArc (finRotate n C.column)) (hs : C.turnRow = G.X C.column) :
    letI := hG.unblockedHomologyModule R
    letI := (hG.swapColumns C.column (finRotate n C.column)).unblockedHomologyModule R
    LinearMap.IsHomogeneous (hG.unblockedHomologyCommutationLinearMap R C)
      (hG.alexanderUnblockedHomologyGrading R).piece
      ((hG.swapColumns C.column (finRotate n C.column)).alexanderUnblockedHomologyGrading R).piece
      (-1) := by
  simpa [commutationBidegree_eq_of_notMem_columnArc C h hO hs] using
    hG.isHomogeneous_unblockedHomologyCommutationLinearMap R C

end IsKnot

end GridDiagram

end TauCeti
