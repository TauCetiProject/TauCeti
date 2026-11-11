/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Filtered.Alexander
public import TauCeti.KnotTheory.Grid.Grading.CyclicPermutation

/-!
# The filtered grid complex under cyclic permutation

The filtered grid complex of a grid diagram `G` is the free module `GC⁻` on grid states over
`R[V₀, …, V_{n-1}]` with the filtered differential, which counts every empty rectangle with the
weight `V^{O(r)}` of the `O`-markings it covers, together with the Alexander filtration
`F_a = G.alexanderFiltration R a` (`TauCeti.KnotTheory.Grid.Filtered.Alexander`). The
differential squares to zero when `R` has characteristic two
(`TauCeti.GridDiagram.filteredDifferential_comp_self_eq_zero`), and the filtered chain homotopy
type of the resulting complex is the knot invariant of Ozsváth, Stipsicz and Szabó. This file
treats the simplest grid moves, the cyclic permutations of the rows and of the columns
(`GridDiagram.IsMove.cyclicRows`, `GridDiagram.IsMove.cyclicColumns`). For both, relabeling every
grid state by the same cyclic permutation intertwines the filtered differentials and preserves
the Alexander filtration over any commutative semiring `R`; in characteristic two it is therefore
an isomorphism of filtered chain complexes from the filtered complex of `G` to that of the
permuted diagram.

A cyclic permutation carries the empty rectangles from `x` to `y` bijectively to the empty
rectangles between the relabeled states (`GridRectangleBetween.isEmpty_relabelRowsEquiv_finRotate`,
`GridRectangleBetween.isEmpty_relabelColumnsEquiv_finRotate`), and the `O`-markings they cover
with them. For the rows the variables, which are indexed by columns, are untouched, and the chain
relabeling `GridChain.relabelRowsEquiv` is linear over the polynomial ring. For the columns the
weights are renamed by the same permutation, so the chain map is the semilinear relabeling
`GridChain.relabelColumnsRenameEquiv`, which also renames the variables in the coefficients. Both
maps preserve the Alexander grading of grid states
(`OddComponentGridDiagram.alexanderℤ_relabelRows_finRotate`,
`OddComponentGridDiagram.alexanderℤ_relabelColumns_finRotate`) and the total degree of monomials,
so they carry each level `F_a` of the Alexander filtration exactly onto the level `F_a` of the
permuted diagram.

## Main results

* `TauCeti.GridDiagram.filteredCoefficient_relabelRows_finRotate`,
  `TauCeti.GridDiagram.filteredCoefficient_relabelColumns_finRotate`: the matrix coefficients of
  the filtered differential of a cyclically permuted diagram.
* `TauCeti.GridDiagram.filteredDifferential_relabelRows_finRotate`: the row relabeling
  intertwines the filtered differentials.
* `TauCeti.GridDiagram.filteredDifferential_relabelColumns_finRotate`: the column relabeling,
  followed by renaming the variables, intertwines the filtered differentials.
* `TauCeti.OddComponentGridDiagram.relabelRowsEquiv_finRotate_mem_alexanderFiltration_iff`,
  `TauCeti.OddComponentGridDiagram.relabelColumnsRenameEquiv_finRotate_mem_alexanderFiltration_iff`:
  the two relabelings preserve and reflect every level of the Alexander filtration.
* `TauCeti.OddComponentGridDiagram.map_relabelRowsEquiv_finRotate_alexanderFiltration`,
  `TauCeti.OddComponentGridDiagram.map_relabelColumnsRenameEquiv_finRotate_alexanderFiltration`:
  they carry each level of the Alexander filtration onto the corresponding level of the permuted
  diagram.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 13 (the filtered grid complex and the invariance of its
  filtered quasi-isomorphism type under grid moves).
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

open GridRectangleBetween

/-! ### Cyclic permutation of the rows -/

/-- A cyclic permutation of the rows leaves the matrix coefficients of the filtered differential
unchanged. -/
@[simp]
theorem filteredCoefficient_relabelRows_finRotate (x y : GridState n) :
    (G.relabelRows (finRotate n)).filteredCoefficient R (x.relabelRows (finRotate n))
        (y.relabelRows (finRotate n)) =
      G.filteredCoefficient R x y := by
  rw [filteredCoefficient_def, filteredCoefficient_def]
  refine (Finset.sum_equiv (relabelRowsEquiv (finRotate n) x y) (fun r => ?_)
    fun r _ => (G.OMonomial_relabelRows_finRotate R r).symm).symm
  simp only [mem_emptyRectangles, isEmpty_relabelRowsEquiv_finRotate]

/-- The chain relabeling by a cyclic permutation of the rows intertwines the filtered
differentials of `G` and of the row-permuted diagram. -/
theorem filteredDifferential_relabelRows_finRotate :
    (G.relabelRows (finRotate n)).filteredDifferential R ∘ₗ
        (GridChain.relabelRowsEquiv (finRotate n)).toLinearMap =
      (GridChain.relabelRowsEquiv (finRotate n)).toLinearMap ∘ₗ G.filteredDifferential R := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelRows (finRotate n) = y :=
    ⟨y.relabelRows (finRotate n).symm, by simp⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
    GridChain.relabelRowsEquiv_single, filteredDifferential_single_apply,
    GridChain.relabelRowsEquiv_apply_relabelRows, filteredCoefficient_relabelRows_finRotate]

/-- The chain relabeling by a cyclic permutation of the rows intertwines the filtered
differentials pointwise. -/
@[simp]
theorem filteredDifferential_relabelRows_finRotate_apply (c : GridChainMinus R n) :
    (G.relabelRows (finRotate n)).filteredDifferential R
        (GridChain.relabelRowsEquiv (finRotate n) c) =
      GridChain.relabelRowsEquiv (finRotate n) (G.filteredDifferential R c) :=
  LinearMap.congr_fun (G.filteredDifferential_relabelRows_finRotate R) c

/-! ### Cyclic permutation of the columns -/

/-- A cyclic permutation of the columns renames the variables in the matrix coefficients of the
filtered differential. -/
@[simp]
theorem filteredCoefficient_relabelColumns_finRotate (x y : GridState n) :
    (G.relabelColumns (finRotate n)).filteredCoefficient R (x.relabelColumns (finRotate n))
        (y.relabelColumns (finRotate n)) =
      rename (finRotate n) (G.filteredCoefficient R x y) := by
  rw [filteredCoefficient_def, filteredCoefficient_def, map_sum]
  refine (Finset.sum_equiv (relabelColumnsEquiv (finRotate n) x y) (fun r => ?_)
    fun r _ => (G.OMonomial_relabelColumns_finRotate R r).symm).symm
  simp only [mem_emptyRectangles, isEmpty_relabelColumnsEquiv_finRotate]

/-- The chain relabeling by a cyclic permutation of the columns, which also renames the variables
of the coefficients by the same permutation, intertwines the filtered differentials of `G` and of
the column-permuted diagram. -/
theorem filteredDifferential_relabelColumns_finRotate :
    ((G.relabelColumns (finRotate n)).filteredDifferential R).comp
        (GridChain.relabelColumnsRenameEquiv R (finRotate n)).toLinearMap =
      (GridChain.relabelColumnsRenameEquiv R (finRotate n)).toLinearMap.comp
        (G.filteredDifferential R) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun y => ?_)
  obtain ⟨y, rfl⟩ : ∃ y', y'.relabelColumns (finRotate n) = y :=
    ⟨y.relabelColumns (finRotate n).symm, by simp⟩
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    GridChain.relabelColumnsRenameEquiv_single, map_one, filteredDifferential_single_apply,
    LinearEquiv.coe_coe, GridChain.relabelColumnsRenameEquiv_apply_relabelColumns,
    filteredCoefficient_relabelColumns_finRotate, one_mul]

/-- The chain relabeling by a cyclic permutation of the columns, followed by renaming the
variables, intertwines the filtered differentials pointwise. -/
@[simp]
theorem filteredDifferential_relabelColumns_finRotate_apply (c : GridChainMinus R n) :
    (G.relabelColumns (finRotate n)).filteredDifferential R
        (GridChain.relabelColumnsRenameEquiv R (finRotate n) c) =
      GridChain.relabelColumnsRenameEquiv R (finRotate n) (G.filteredDifferential R c) :=
  LinearMap.congr_fun (G.filteredDifferential_relabelColumns_finRotate R) c

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommSemiring R]

/-! ### The Alexander filtration -/

variable {G R} in
/-- Relabeling the grid states along a cyclic permutation of the rows preserves and reflects each
level of the Alexander filtration. -/
theorem relabelRowsEquiv_finRotate_mem_alexanderFiltration_iff {a : ℤ} {c : GridChainMinus R n} :
    GridChain.relabelRowsEquiv (finRotate n) c ∈
        (G.relabelRows (finRotate n)).alexanderFiltration R a ↔
      c ∈ G.alexanderFiltration R a := by
  rw [mem_alexanderFiltration, mem_alexanderFiltration,
    GridChain.forall_mem_support_relabelRowsEquiv_iff]
  simp only [alexanderℤ_relabelRows_finRotate]

/-- Relabeling the grid states along a cyclic permutation of the rows carries each level of the
Alexander filtration of `G` onto the same level of the row-permuted diagram. -/
@[simp]
theorem map_relabelRowsEquiv_finRotate_alexanderFiltration (a : ℤ) :
    (G.alexanderFiltration R a).map (GridChain.relabelRowsEquiv (finRotate n)).toLinearMap =
      (G.relabelRows (finRotate n)).alexanderFiltration R a := by
  ext c
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap,
    ← relabelRowsEquiv_finRotate_mem_alexanderFiltration_iff, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

variable {G R} in
/-- Relabeling the grid states along a cyclic permutation of the columns, and renaming the
variables along the same permutation, preserves and reflects each level of the Alexander
filtration. -/
theorem relabelColumnsRenameEquiv_finRotate_mem_alexanderFiltration_iff {a : ℤ}
    {c : GridChainMinus R n} :
    GridChain.relabelColumnsRenameEquiv R (finRotate n) c ∈
        (G.relabelColumns (finRotate n)).alexanderFiltration R a ↔
      c ∈ G.alexanderFiltration R a := by
  rw [mem_alexanderFiltration, mem_alexanderFiltration,
    GridChain.forall_mem_support_relabelColumnsRenameEquiv_iff]
  simp only [alexanderℤ_relabelColumns_finRotate, Finsupp.degree_mapDomain]

/-- Relabeling the grid states along a cyclic permutation of the columns, and renaming the
variables along the same permutation, carries each level of the Alexander filtration of `G` onto
the same level of the column-permuted diagram. -/
@[simp]
theorem map_relabelColumnsRenameEquiv_finRotate_alexanderFiltration (a : ℤ) :
    (G.alexanderFiltration R a).map
        (GridChain.relabelColumnsRenameEquiv R (finRotate n)).toLinearMap =
      (G.relabelColumns (finRotate n)).alexanderFiltration R a := by
  ext c
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap,
    ← relabelColumnsRenameEquiv_finRotate_mem_alexanderFiltration_iff, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

end OddComponentGridDiagram

end TauCeti
