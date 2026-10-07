/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold
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

/-- The open star of a vertex consists of points with positive barycentric coordinate at
that vertex. Equivalently, their carriers contain the vertex. -/
def openStarRealization (v : ι) : Set (Realization K) := {x | 0 < x.1 v}

/-- The realized closed star consists of points whose carriers lie in the closed star. -/
def closedStarRealization (v : ι) : Set (Realization K) :=
  {x | x.1.support ∈ PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}}

omit [DecidableEq ι] in
/-- Membership in the open star is positivity of the corresponding coordinate. -/
@[simp]
theorem mem_openStarRealization {v : ι} {x : Realization K} :
    x ∈ K.openStarRealization v ↔ 0 < x.1 v := Iff.rfl

/-- Membership in the realized closed star is closed-star membership of the carrier. -/
@[simp]
theorem mem_closedStarRealization {v : ι} {x : Realization K} :
    x ∈ K.closedStarRealization v ↔
      x.1.support ∈ PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v} :=
  Iff.rfl

omit [DecidableEq ι] in
/-- A point lies in the open star exactly when its carrier contains the vertex. -/
theorem mem_openStarRealization_iff_mem_support {v : ι} {x : Realization K} :
    x ∈ K.openStarRealization v ↔ v ∈ x.1.support := by
  rw [mem_openStarRealization, Finsupp.mem_support_iff]
  exact (lt_iff_le_and_ne).trans (by simp [Realization.nonneg K x v, ne_comm])

omit [DecidableEq ι] in
/-- Open stars are open for the weak topology, since coordinates are continuous. -/
theorem isOpen_openStarRealization (v : ι) : IsOpen (K.openStarRealization v) :=
  isOpen_lt continuous_const ((continuous_apply v).comp (continuous_realization_coe K))

omit [DecidableEq ι] in
/-- Every realization point belongs to an open vertex star. -/
theorem exists_mem_openStarRealization (x : Realization K) :
    ∃ v, x ∈ K.openStarRealization v := by
  classical
  obtain ⟨v, hv⟩ := K.isRelLowerSet_faces.prop_of_mem (support_mem K x)
  exact ⟨v, (K.mem_openStarRealization_iff_mem_support).mpr hv⟩

omit [DecidableEq ι] in
/-- The open vertex stars cover the realization. -/
@[simp]
theorem iUnion_openStarRealization : ⋃ v, K.openStarRealization v = univ :=
  Set.eq_univ_of_forall fun x => mem_iUnion.mpr (K.exists_mem_openStarRealization x)

/-- Each open star lies in its closed star. -/
theorem openStarRealization_subset_closedStarRealization (v : ι) :
    K.openStarRealization v ⊆ K.closedStarRealization v := by
  intro x hx
  apply PreAbstractSimplicialComplex.mem_closedStar.mpr
  refine ⟨support_mem K x, ?_⟩
  rw [Finset.union_singleton,
    Finset.insert_eq_of_mem ((K.mem_openStarRealization_iff_mem_support).mp hx)]
  exact support_mem K x

/-- The realization of a finite closed star is compact. -/
theorem isCompact_closedStarRealization {v : ι}
    (hfin :
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    IsCompact (K.closedStarRealization v) :=
  K.isCompact_setOf_support_mem PreAbstractSimplicialComplex.closedStar_le hfin

/-- Finite vertex stars provide a compact neighbourhood around every realization point. -/
theorem locallyCompactSpace_realization_of_finite_vertex_stars
    (hfin : ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    LocallyCompactSpace (Realization K) := by
  have : WeaklyLocallyCompactSpace (Realization K) := ⟨fun x => by
    obtain ⟨v, hv⟩ := K.exists_mem_openStarRealization x
    exact ⟨K.closedStarRealization v, K.isCompact_closedStarRealization (hfin v),
      mem_of_superset ((K.isOpen_openStarRealization v).mem_nhds hv)
        (K.openStarRealization_subset_closedStarRealization v)⟩⟩
  infer_instance

/-- With finite vertex stars, the weak topology is exactly the topology induced by
barycentric coordinates. No global finiteness assumption is needed. -/
theorem isEmbedding_realization_coe_of_finite_vertex_stars
    (hfin : ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite) :
    Topology.IsEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) := by
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
    let C := K.closedStarRealization v
    have : CompactSpace C :=
      isCompact_iff_compactSpace.mp (K.isCompact_closedStarRealization (hfin v))
    have hC : Topology.IsEmbedding (fun x : C => c x.1) :=
      ((continuous_realization_coe K).comp continuous_subtype_val).isClosedEmbedding
        ((injective_realization_coe K).comp Subtype.val_injective) |>.isEmbedding
    have hsub : (rangeFactorization c) ⁻¹' (U v) ⊆ C := by
      rw [hpreimage v]
      exact K.openStarRealization_subset_closedStarRealization v
    have hi := hC.comp (Topology.IsEmbedding.inclusion hsub)
    -- Forget the two range subtypes to compare the restricted coordinate map with
    -- its factorization through the compact closed star.
    exact (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).of_comp_iff.mp hi
  exact Topology.IsEmbedding.subtypeVal.comp he

/-- The realization of a combinatorial manifold is locally compact. -/
theorem locallyCompactSpace_realization_of_isCombinatorialManifold {n : ℕ}
    (hK : PreAbstractSimplicialComplex.IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) :
    LocallyCompactSpace (Realization K) :=
  K.locallyCompactSpace_realization_of_finite_vertex_stars fun v =>
    hK.finite_faces_closedStar (K.singleton_mem v)

/-- The weak realization of a combinatorial manifold embeds in its barycentric-coordinate
space. -/
theorem isEmbedding_realization_coe_of_isCombinatorialManifold {n : ℕ}
    (hK : PreAbstractSimplicialComplex.IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) :
    Topology.IsEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) :=
  K.isEmbedding_realization_coe_of_finite_vertex_stars fun v =>
    hK.finite_faces_closedStar (K.singleton_mem v)

end AbstractSimplicialComplex
