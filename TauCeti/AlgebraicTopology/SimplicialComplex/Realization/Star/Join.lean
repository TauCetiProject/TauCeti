/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Star
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Basic

/-!
# Geometric join coordinates on closed face stars

The closed star of a face `σ` is homeomorphic to the weak polyhedron of the join of the
simplex on `σ` with its link. The homeomorphism tags coordinates belonging to `σ` on the left
and the remaining coordinates on the right. Its restriction identifies the part avoiding the
whole face `σ` with the join of the boundary of `σ` and its link. The two homeomorphisms
commute with the inclusions of these subpolyhedra.

These are identifications of pairs, used to pass from face stars to their standard join
models. The part avoiding `σ` is a combinatorial boundary; it need not be the topological
frontier of the closed star in the ambient polyhedron. In particular, no manifold condition
is imposed. Void links, singleton faces, and maximal faces are included.

The topology is the weak topology, with no finiteness or local-finiteness assumption. The
construction transports the combinatorial identities of `Join.Star` through
`PreAbstractSimplicialComplex.relabelingHomeomorph`, whose continuity is tested on simplices.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (stars, links, and joins).
-/

public noncomputable section

open AbstractSimplicialComplex TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι)
  {A : AbstractSimplicialComplex ι} {σ : Finset ι}

/-- Tagging vertices by membership in `σ` identifies its closed star with the weak polyhedron
of the join of the simplex on `σ` and its link. Unused tagged vertices contribute no points. -/
def closedStarJoinHomeomorph (hσ : σ ∈ K) (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    {x : Realization A // x.1.support ∈ closedStar K σ} ≃ₜ
      {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) //
        y.1.support ∈ PreAbstractSimplicialComplex.join (simplex σ) (link K σ)} :=
  ((closedStar K σ).relabelingHomeomorph
    (partitionEmbedding (· ∈ σ)) (closedStar_le.trans hK) (by
      rw [map_closedStar_eq_join hσ]
      exact PreAbstractSimplicialComplex.le_top _)).trans
    (Homeomorph.setCongr
      (s := {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) |
        y.1.support ∈ (closedStar K σ).map (partitionEmbedding (· ∈ σ))})
      (t := {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) |
        y.1.support ∈ PreAbstractSimplicialComplex.join (simplex σ) (link K σ)})
      (by rw [map_closedStar_eq_join hσ]))

/-- The join coordinates are the pushforward of the original barycentric coordinates. -/
@[simp]
theorem closedStarJoinHomeomorph_val (hσ : σ ∈ K) (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (x : {x : Realization A // x.1.support ∈ closedStar K σ}) :
    (K.closedStarJoinHomeomorph hσ hK x).1.1 =
      Finsupp.mapDomain (partitionEmbedding (· ∈ σ)) x.1.1 := by
  -- `erw` reduces the set-like coercions in the intermediate subpolyhedron.
  erw [closedStarJoinHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  exact relabelingHomeomorph_val _ _ _ _ x

/-- The inverse join coordinates pull back along the tagging of the vertices. -/
@[simp]
theorem closedStarJoinHomeomorph_symm_val (hσ : σ ∈ K) (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (y : {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) //
      y.1.support ∈ PreAbstractSimplicialComplex.join (simplex σ) (link K σ)}) :
    ((K.closedStarJoinHomeomorph hσ hK).symm y).1.1 =
      Finsupp.comapDomain (partitionEmbedding (· ∈ σ)) y.1.1
        (partitionEmbedding (· ∈ σ)).injective.injOn := by
  -- `erw` reduces the set-like coercions in the intermediate subpolyhedron.
  erw [closedStarJoinHomeomorph, Homeomorph.symm_trans_apply,
    Homeomorph.setCongr_symm_apply]
  exact relabelingHomeomorph_symm_val _ _ _ _ _

/-- The support in the left factor is precisely the part of the original support in `σ`;
the support in the right factor is its complement. -/
theorem closedStarJoinHomeomorph_support (hσ : σ ∈ K) (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (x : {x : Realization A // x.1.support ∈ closedStar K σ}) :
    (K.closedStarJoinHomeomorph hσ hK x).1.1.support =
      (x.1.1.support ∩ σ).disjSum (x.1.1.support \ σ) := by
  rw [closedStarJoinHomeomorph_val, Finsupp.mapDomain_support_of_injective
    (partitionEmbedding (· ∈ σ)).injective, Finset.image_partitionEmbedding]
  simp only [Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff]

/-- A point of the closed star lies in the boundary join exactly when its carrier does not
contain the whole starred face. -/
theorem closedStarJoinHomeomorph_mem_boundary_iff (hσ : σ ∈ K)
    (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (x : {x : Realization A // x.1.support ∈ closedStar K σ}) :
    (K.closedStarJoinHomeomorph hσ hK x).1.1.support ∈
        PreAbstractSimplicialComplex.join (simplexBoundary σ) (link K σ) ↔
      ¬ σ ⊆ x.1.1.support := by
  rw [← map_closedStar_inf_deletion_eq_join hσ, closedStarJoinHomeomorph_val,
    Finsupp.mapDomain_support_of_injective (partitionEmbedding (· ∈ σ)).injective,
    mem_map_iff]
  simp only [Finset.image_inj (partitionEmbedding (· ∈ σ)).injective, exists_eq_right,
    mem_inf, mem_deletion, x.2, true_and]
  exact and_iff_right (closedStar_le x.2)

/-- The part of a closed star avoiding `σ` is homeomorphic to the weak polyhedron of the
join of the boundary of `σ` and its link. This uses the same tagging as
`closedStarJoinHomeomorph`. -/
def closedStarBoundaryJoinHomeomorph (hσ : σ ∈ K) (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    {x : Realization A // x.1.support ∈ closedStar K σ ⊓
      deletion K σ} ≃ₜ
      {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) //
        y.1.support ∈ PreAbstractSimplicialComplex.join (simplexBoundary σ) (link K σ)} :=
  ((closedStar K σ ⊓
      deletion K σ).relabelingHomeomorph
    (partitionEmbedding (· ∈ σ)) (inf_le_left.trans (closedStar_le.trans hK)) (by
      rw [map_closedStar_inf_deletion_eq_join hσ]
      exact PreAbstractSimplicialComplex.le_top _)).trans
    (Homeomorph.setCongr
      (s := {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) |
        y.1.support ∈ (closedStar K σ ⊓ deletion K σ).map (partitionEmbedding (· ∈ σ))})
      (t := {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) |
        y.1.support ∈ PreAbstractSimplicialComplex.join (simplexBoundary σ) (link K σ)})
      (by rw [map_closedStar_inf_deletion_eq_join hσ]))

/-- The boundary join homeomorphism pushes forward the barycentric coordinates by tagging. -/
@[simp]
theorem closedStarBoundaryJoinHomeomorph_val (hσ : σ ∈ K)
    (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (x : {x : Realization A // x.1.support ∈ closedStar K σ ⊓
      deletion K σ}) :
    (K.closedStarBoundaryJoinHomeomorph hσ hK x).1.1 =
      Finsupp.mapDomain (partitionEmbedding (· ∈ σ)) x.1.1 := by
  -- `erw` reduces the set-like coercions in the intermediate subpolyhedron.
  erw [closedStarBoundaryJoinHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  exact relabelingHomeomorph_val _ _ _ _ x

/-- The inverse boundary join coordinates pull back along the tagging of the vertices. -/
@[simp]
theorem closedStarBoundaryJoinHomeomorph_symm_val (hσ : σ ∈ K)
    (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (y : {y : Realization (⊤ : AbstractSimplicialComplex (ι ⊕ ι)) //
      y.1.support ∈ PreAbstractSimplicialComplex.join (simplexBoundary σ) (link K σ)}) :
    ((K.closedStarBoundaryJoinHomeomorph hσ hK).symm y).1.1 =
      Finsupp.comapDomain (partitionEmbedding (· ∈ σ)) y.1.1
        (partitionEmbedding (· ∈ σ)).injective.injOn := by
  -- `erw` reduces the set-like coercions in the intermediate subpolyhedron.
  erw [closedStarBoundaryJoinHomeomorph, Homeomorph.symm_trans_apply,
    Homeomorph.setCongr_symm_apply]
  exact relabelingHomeomorph_symm_val _ _ _ _ _

/-- The closed-star and boundary-join identifications commute with the inclusions. -/
theorem closedStarBoundaryJoinHomeomorph_coe (hσ : σ ∈ K)
    (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (x : {x : Realization A // x.1.support ∈ closedStar K σ ⊓
      deletion K σ}) :
    (K.closedStarBoundaryJoinHomeomorph hσ hK x).1 =
      (K.closedStarJoinHomeomorph hσ hK ⟨x.1, (mem_inf.mp x.2).1⟩).1 := by
  apply Subtype.ext
  simp only [closedStarBoundaryJoinHomeomorph_val, closedStarJoinHomeomorph_val]

end PreAbstractSimplicialComplex
