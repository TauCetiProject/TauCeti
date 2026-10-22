/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic

/-!
# Incidence support for simplicial realization cells

The cellular boundary of a simplex is supported on its codimension-one faces.  This file proves
the support statement for the classical CW structure on the weak realization of an abstract
simplicial complex: if an `n`-cell is not a face of an `(n + 1)`-cell, their cellular incidence
coefficient is zero.  Equivalently, the cellular boundary column is supported on the cells
obtained by deleting one vertex.

The proof uses the local-degree description of cellular incidence.  The barycentre picked out by
the origin of an `n`-cell's characteristic map lies in its open cell.  If the cell is not a face
of the larger simplex, that point is absent from the larger cell's frontier, so the attaching map
has local degree zero there.

Computing the nonzero coefficients, including their alternating signs in the increasing vertex
order, is a separate orientation calculation.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1--2.2.
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

/-- The support of a cellular boundary column is contained in the codimension-one faces of the
source simplicial cell. -/
theorem support_cellularBoundaryColumn_realization_subset_faces
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    letI := _root_.AbstractSimplicialComplex.realizationCWComplex K
    (cellularBoundaryColumn
        (Set.univ : Set (_root_.AbstractSimplicialComplex.Realization K)) R n
        (_root_.AbstractSimplicialComplex.realizationCellEquiv K (n + 1) |>.symm c)).mapDomain
          (_root_.AbstractSimplicialComplex.realizationCellEquiv K n) |>.support ⊆
      Finset.univ.image c.face := by
  let := _root_.AbstractSimplicialComplex.realizationCWComplex K
  intro d hd
  rw [Finsupp.mapDomain_support_of_injective
    (_root_.AbstractSimplicialComplex.realizationCellEquiv K n).injective] at hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  rw [Finsupp.mem_support_iff, cellularBoundaryColumn_apply] at hi
  rw [Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  exact (c.exists_face_eq_iff_subset
    (_root_.AbstractSimplicialComplex.realizationCellEquiv K n i)).2 <| by
      by_contra hsubset
      apply hi
      simpa only [Equiv.symm_apply_apply] using
        cellularIncidence_realization_eq_zero_of_not_subset (R := R) c _ hsubset

end TauCeti
