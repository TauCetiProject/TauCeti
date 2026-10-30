/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Regular
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic

/-!
# Incidence numbers of simplicial realization cells

The cellular boundary of a simplex is supported on its codimension-one faces, with unit
coefficients.  This file proves both statements for the classical CW structure on the weak
realization of an abstract simplicial complex.

* If an `n`-cell is not a face of an `(n + 1)`-cell, their cellular incidence coefficient is zero
  (`TauCeti.cellularIncidence_realization_eq_zero_of_not_subset`).  Equivalently, the cellular
  boundary column is supported on the cells obtained by deleting one vertex
  (`TauCeti.support_cellularBoundaryColumn_realization_subset_faces`).  The barycentre picked out
  by the origin of an `n`-cell's characteristic map lies in its open cell.  If the cell is not a
  face of the larger simplex, that point is absent from the larger cell's frontier, so the
  attaching map has local degree zero there.
  Hence the cellular boundary of a cell is the sum over its deleted-vertex faces of their
  incidence coefficients times their basis vectors
  (`TauCeti.cellularDifferential_realization_cellularChainBasis`).
* The attaching map of a simplicial cell is injective
  (`TauCeti.cellAttachingMap_realization_injective`): the realization is a regular CW complex.
  Hence the incidence coefficient of a positive-dimensional codimension-one face is a unit of the
  coefficient ring (`TauCeti.isUnit_cellularIncidence_realization_of_subset`), so `±1` over `ℤ`.

Computing the signs of these units, which alternate in the increasing vertex order, is a separate
orientation calculation.  The faces of a `1`-simplex, where the boundary sphere is `S⁰`, are not
treated here.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1--2.2.
* A. T. Lundell, S. Weingram, *The Topology of CW Complexes*, Van Nostrand Reinhold (1969),
  Chapter V (regular CW complexes).
-/

public section

noncomputable section

open CategoryTheory Finsupp Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {ι : Type u} [LinearOrder ι]
variable (K : _root_.AbstractSimplicialComplex ι)
variable (R : Type u) [Ring R]

variable {K R} {n : ℕ}

/-- The origin in the characteristic coordinates of a realization cell, regarded as a point of
the cell's weak realization. -/
private noncomputable def center
    (d : _root_.AbstractSimplicialComplex.RealizationCell K n) :
    _root_.AbstractSimplicialComplex.Realization K :=
  d.characteristicMap 0

private theorem support_center
    (d : _root_.AbstractSimplicialComplex.RealizationCell K n) :
    (center d).1.support = d.1.1 := by
  have hzero : (0 : Fin n → ℝ) ∈ d.characteristicMap.source := by
    rw [_root_.AbstractSimplicialComplex.RealizationCell.characteristicMap_source,
      mem_ball_zero_iff, norm_zero]
    exact zero_lt_one
  simpa only [center,
    _root_.AbstractSimplicialComplex.RealizationCell.characteristicMap_target,
    Set.mem_ofPred_eq] using d.characteristicMap.map_source hzero

private theorem center_mem_openCell
    (d : _root_.AbstractSimplicialComplex.RealizationCell K n) :
    letI := _root_.AbstractSimplicialComplex.realizationCWComplex K
    center d ∈ openCell n
      ((_root_.AbstractSimplicialComplex.realizationCellEquiv K n).symm d) := by
  let := _root_.AbstractSimplicialComplex.realizationCWComplex K
  rw [_root_.AbstractSimplicialComplex.openCell_realizationCellEquiv_symm]
  exact support_center d

private theorem center_not_mem_cellFrontier_of_not_subset
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1))
    (d : _root_.AbstractSimplicialComplex.RealizationCell K n)
    (h : ¬ d.1.1 ⊆ c.1.1) :
    letI := _root_.AbstractSimplicialComplex.realizationCWComplex K
    center d ∉ cellFrontier (n + 1)
      ((_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 1)).symm c) := by
  let := _root_.AbstractSimplicialComplex.realizationCWComplex K
  rw [_root_.AbstractSimplicialComplex.cellFrontier_realizationCellEquiv_symm]
  intro hcenter
  apply h
  exact support_center d ▸ hcenter.subset

/-- A cell which is not a codimension-one subface has zero cellular incidence coefficient in the
boundary of the larger simplicial cell. -/
theorem cellularIncidence_realization_eq_zero_of_not_subset
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1))
    (d : _root_.AbstractSimplicialComplex.RealizationCell K n)
    (h : ¬ d.1.1 ⊆ c.1.1) :
    letI := _root_.AbstractSimplicialComplex.realizationCWComplex K
    cellularIncidence (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K))
      R n (_root_.AbstractSimplicialComplex.realizationCellEquiv K n |>.symm d)
        (_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 1) |>.symm c) = 0 := by
  let := _root_.AbstractSimplicialComplex.realizationCWComplex K
  let x : skeletonObj
      (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) (n + 1) :=
    ⟨center d, openCell_subset_skeletonLT n _ (center_mem_openCell d)⟩
  exact cellularIncidence_eq_zero_of_not_mem_cellFrontier
    (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) R x
      (center_mem_openCell d) _ (center_not_mem_cellFrontier_of_not_subset c d h)

open scoped Classical in
/-- The support of a cellular boundary column is contained in the codimension-one faces of the
source simplicial cell. -/
theorem support_cellularBoundaryColumn_realization_subset_faces
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    letI := _root_.AbstractSimplicialComplex.realizationCWComplex K
    (cellularBoundaryColumn
        (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) R n
        (_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 1) |>.symm c)).support ⊆
      Finset.univ.image fun j ↦
        (_root_.AbstractSimplicialComplex.realizationCellEquiv K n).symm (c.face j) := by
  let := _root_.AbstractSimplicialComplex.realizationCWComplex K
  intro d hd
  rw [Finsupp.mem_support_iff, cellularBoundaryColumn_apply] at hd
  obtain ⟨j, hj⟩ := (c.exists_face_eq_iff_subset
    (_root_.AbstractSimplicialComplex.realizationCellEquiv K n d)).2 <| by
      by_contra hsubset
      apply hd
      simpa only [Equiv.symm_apply_apply] using
        cellularIncidence_realization_eq_zero_of_not_subset (R := R) c _ hsubset
  exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, by rw [hj, Equiv.symm_apply_apply]⟩

/-- **The cellular boundary of a simplicial cell** is the finite sum, over its deleted-vertex
faces, of their incidence coefficients times their cellular basis vectors. -/
theorem cellularDifferential_realization_cellularChainBasis
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    letI := _root_.AbstractSimplicialComplex.realizationCWComplex K
    cellularDifferential (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K))
        (ModuleCat.of R R) n
        (cellularChainBasis (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) R
          (n + 1) ((_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 1)).symm c)) =
      ∑ j : Fin (n + 2),
        (cellularIncidence (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) R n
            ((_root_.AbstractSimplicialComplex.realizationCellEquiv K n).symm (c.face j))
            ((_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 1)).symm c) : R) •
          (cellularChainBasis (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) R
            n ((_root_.AbstractSimplicialComplex.realizationCellEquiv K n).symm (c.face j)) :
              (cellularChainGroup (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K))
                (ModuleCat.of R R) n : ModuleCat R)) := by
  let := _root_.AbstractSimplicialComplex.realizationCWComplex K
  classical
  rw [cellularDifferential_basis, Finsupp.sum_of_support_subset _
    (support_cellularBoundaryColumn_realization_subset_faces c)
    (fun i a ↦ a • cellularChainBasis
      (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) R n i) (by simp)]
  rw [Finset.sum_image fun j _ k _ h ↦
    c.face_injective ((_root_.AbstractSimplicialComplex.realizationCellEquiv K n).symm.injective h)]
  simp only [cellularBoundaryColumn_apply]

/-- **Codimension-one faces have unit incidence numbers.** The incidence coefficient of a
positive-dimensional face `d` of a simplicial cell `c`, with one vertex fewer, in the cellular
boundary of `c` is a unit of the coefficient ring. -/
theorem isUnit_cellularIncidence_realization_of_subset
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 2))
    (d : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1))
    (h : d.1.1 ⊆ c.1.1) :
    letI := _root_.AbstractSimplicialComplex.realizationCWComplex K
    IsUnit (cellularIncidence (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K))
      R (n + 1) (_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 1) |>.symm d)
        (_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 2) |>.symm c)) := by
  let := _root_.AbstractSimplicialComplex.realizationCWComplex K
  refine isUnit_cellularIncidence_of_injective _ R (cellAttachingMap_realization_injective c) ?_
  rw [_root_.AbstractSimplicialComplex.openCell_realizationCellEquiv_symm,
    _root_.AbstractSimplicialComplex.cellFrontier_realizationCellEquiv_symm]
  intro x hx
  rw [Set.mem_ofPred_eq] at hx ⊢
  rw [hx]
  refine Finset.ssubset_iff_subset_ne.2 ⟨h, fun hdc ↦ ?_⟩
  have hcard := congrArg Finset.card hdc
  rw [d.2, c.2] at hcard
  omega

end TauCeti
