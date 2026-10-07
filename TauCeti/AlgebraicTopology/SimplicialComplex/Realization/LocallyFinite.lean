/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import Mathlib.Topology.LocalAtTarget

/-!
# Locally finite polyhedra

When every vertex has finite closed star, a weak geometric realization is locally compact
and its topology agrees with the topology of its barycentric coordinates. The open stars
are the coordinate-positive neighbourhoods; each lies in a compact closed star. This permits
local models of combinatorial manifolds to be treated as coordinate subspaces without a
global finiteness assumption on the triangulation.

The sphere-or-ball link condition implies finiteness of every vertex star. Consequently
realizations of combinatorial manifolds satisfy both conclusions.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2--3 (locally finite polyhedra and vertex stars).
-/

public section

noncomputable section

open Set Filter Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι)

/-- Finite vertex stars provide a compact neighbourhood around every realization point. -/
theorem locallyCompactSpace_realization_of_finite_vertex_stars
    (hfin : ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    LocallyCompactSpace (Realization K) := by
  have : WeaklyLocallyCompactSpace (Realization K) := ⟨fun x => by
    obtain ⟨v, hv⟩ := K.exists_mem_openStarRealization x
    exact ⟨K.closedStarRealization {v}, K.isCompact_closedStarRealization (hfin v),
      mem_of_superset ((K.isOpen_openStarRealization v).mem_nhds hv)
        (K.openStarRealization_subset_closedStarRealization v)⟩⟩
  infer_instance

/-- With finite vertex stars, the weak topology is exactly the topology induced by
barycentric coordinates. No global finiteness assumption is needed. -/
theorem isEmbedding_realization_coe_of_finite_vertex_stars
    (hfin : ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    Topology.IsEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) := by
  -- Factor coordinates through their range and use its open-star cover.
  -- Check each restriction via the embedding of the compact closed star.
  let c : Realization K → (ι → ℝ) := fun x => x.1
  let U : ι → TopologicalSpace.Opens (range c) := fun v =>
    ⟨{y | 0 < y.1 v}, isOpen_lt continuous_const
      ((continuous_apply v).comp continuous_subtype_val)⟩
  have hpreimage (v : ι) : (rangeFactorization c) ⁻¹' (U v) = K.openStarRealization v := by
    ext x
    simp only [U, TopologicalSpace.Opens.coe_mk, mem_preimage, mem_ofPred_eq,
      mem_openStarRealization, rangeFactorization, c]
  have hcover : TopologicalSpace.IsOpenCover U := by
    refine TopologicalSpace.IsOpenCover.of_sets (fun v => (U v).isOpen) ?_
    apply Set.eq_univ_of_forall
    rintro ⟨_, x, rfl⟩
    obtain ⟨v, hv⟩ := K.exists_mem_openStarRealization x
    have hx : x ∈ (rangeFactorization c) ⁻¹' (U v) := by
      rw [hpreimage v]
      exact hv
    exact mem_iUnion.mpr ⟨v, hx⟩
  have hc : Continuous (rangeFactorization c) := (continuous_realization_coe K).rangeFactorization
  have he : Topology.IsEmbedding (rangeFactorization c) := by
    apply (hcover.isEmbedding_iff_restrictPreimage hc).mpr
    intro v
    let C := K.closedStarRealization {v}
    have hC : Topology.IsEmbedding (fun x : C => c x.1) :=
      (K.isClosedEmbedding_realization_coe_restrict
        (K.isCompact_closedStarRealization (hfin v))).isEmbedding
    have hsub : (rangeFactorization c) ⁻¹' (U v) ⊆ C := by
      rw [hpreimage v]
      exact K.openStarRealization_subset_closedStarRealization v
    have hi := hC.comp (Topology.IsEmbedding.inclusion hsub)
    -- Both sides evaluate to the coordinates of the same realization point:
    -- rangeFactorization, restrictPreimage, and inclusion only add subtype proofs.
    have hcomp : (Subtype.val ∘ Subtype.val) ∘ (U v).1.restrictPreimage (rangeFactorization c) =
        (fun x : C => c x.1) ∘ inclusion hsub := funext fun x => rfl
    rw [← hcomp] at hi
    exact (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).of_comp_iff.mp hi
  exact Topology.IsEmbedding.subtypeVal.comp he

/-- The realization of a combinatorial manifold is locally compact. -/
theorem locallyCompactSpace_realization_of_isCombinatorialManifold {n : ℕ}
    (hK : PreAbstractSimplicialComplex.IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) :
    LocallyCompactSpace (Realization K) :=
  K.locallyCompactSpace_realization_of_finite_vertex_stars fun v =>
    hK.finite_faces_closedStar v

/-- The weak realization of a combinatorial manifold embeds in its barycentric-coordinate
space. -/
theorem isEmbedding_realization_coe_of_isCombinatorialManifold {n : ℕ}
    (hK : PreAbstractSimplicialComplex.IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) :
    Topology.IsEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) :=
  K.isEmbedding_realization_coe_of_finite_vertex_stars fun v =>
    hK.finite_faces_closedStar v

end AbstractSimplicialComplex
