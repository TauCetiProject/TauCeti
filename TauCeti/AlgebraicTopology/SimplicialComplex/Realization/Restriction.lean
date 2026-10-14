/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Restriction
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Compact
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Basic

/-!
# Vertex restrictions and compact factorization

The realization of a vertex restriction is the closed subspace of points supported on those
vertices. In particular, every continuous map from a compact space factors continuously
through a restriction to finitely many vertices. This reduces nullhomotopy constructions
for spheres and cubes in infinite weak polyhedra to finite vertex sets.

The identification uses `PreAbstractSimplicialComplex.relabelingHomeomorph`, rather than
constructing another barycentric pullback. All topologies are weak realization topologies;
neither the complex nor the ambient vertex type needs to be locally finite or countable.

## References

* A. Hatcher, *Algebraic Topology*, Appendix A, Proposition A.1.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

variable (K : AbstractSimplicialComplex ι) (s : Set ι)

/-- Realizing a vertex restriction identifies it with the subspace of points supported on
the chosen vertices. -/
def restrictRealizationHomeomorph :
    Realization (K.restrict s) ≃ₜ {x : Realization K // (x.1.support : Set ι) ⊆ s} := by
  let P := (K.restrict s).toPreAbstractSimplicialComplex
  have hmap : P.map (Function.Embedding.subtype (· ∈ s)) ≤
      K.toPreAbstractSimplicialComplex := fun σ hσ => (mem_map_restrict_iff K s σ).mp hσ |>.1
  let e := P.relabelingHomeomorph (Function.Embedding.subtype (· ∈ s)) le_rfl hmap
  let a : {x : Realization (K.restrict s) // x.1.support ∈ P} ≃ₜ
      Realization (K.restrict s) :=
    (Homeomorph.setCongr (Set.eq_univ_of_forall (support_mem (K.restrict s)))).trans
      (Homeomorph.Set.univ _)
  exact a.symm.trans (e.trans (Homeomorph.setCongr (Set.ext fun x =>
    (mem_map_restrict_iff K s x.1.support).trans (and_iff_right (support_mem K x)))))

/-- The restriction homeomorphism followed by the subtype inclusion is the simplicial
realization of the vertex inclusion. -/
@[simp]
theorem restrictRealizationHomeomorph_apply (x : Realization (K.restrict s)) :
    (K.restrictRealizationHomeomorph s x).1 = (K.restrictInclusion s).realizationMap x := by
  apply Subtype.ext
  dsimp only [restrictRealizationHomeomorph]
  -- `erw` identifies the SetLike coercions of the restriction's underlying precomplex.
  erw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.setCongr_apply,
    Homeomorph.symm_trans_apply, TauCeti.Homeomorph.setCongr_symm_apply,
    PreAbstractSimplicialComplex.relabelingHomeomorph_val]
  · simp only [PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
      coe_restrictInclusion]
    rfl
  · rfl

/-- The inverse restriction homeomorphism pulls barycentric coordinates back along the
vertex inclusion. -/
@[simp]
theorem restrictRealizationHomeomorph_symm_val
    (x : {x : Realization K // (x.1.support : Set ι) ⊆ s}) :
    ((K.restrictRealizationHomeomorph s).symm x).1 =
      Finsupp.comapDomain (Subtype.val : s → ι) x.1.1 Subtype.val_injective.injOn := by
  have h : Finsupp.mapDomain (Subtype.val : s → ι)
      ((K.restrictRealizationHomeomorph s).symm x).1 = x.1.1 := by
    simpa only [restrictRealizationHomeomorph_apply,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val, coe_restrictInclusion] using
      congrArg (fun y => y.1.1) ((K.restrictRealizationHomeomorph s).apply_symm_apply x)
  rw [← h]
  exact (Finsupp.comapDomain_mapDomain _ Subtype.val_injective _).symm

/-- The realized vertex inclusion is a closed embedding, for arbitrary vertex subsets. -/
theorem isClosedEmbedding_restrictInclusion_realizationMap :
    IsClosedEmbedding (K.restrictInclusion s).realizationMap := by
  have hclosed : IsClosed {x : Realization K | (x.1.support : Set ι) ⊆ s} := by
    have hmap : (K.restrict s).toPreAbstractSimplicialComplex.map
        (Function.Embedding.subtype (· ∈ s)) ≤ K.toPreAbstractSimplicialComplex :=
      fun σ hσ => (mem_map_restrict_iff K s σ).mp hσ |>.1
    simpa only [Function.Embedding.coe_subtype, mem_map_restrict_iff, support_mem, true_and] using
      isClosed_setOf_support_mem hmap
  have he := hclosed.isClosedEmbedding_subtypeVal.comp
    (K.restrictRealizationHomeomorph s).isClosedEmbedding
  convert he using 1
  funext x
  exact (restrictRealizationHomeomorph_apply K s x).symm

/-- A point lies in the realized restriction exactly when its support uses only the chosen
vertices. -/
-- Normalize to support containment before `Set.mem_range` expands the existential.
@[simp 1100]
theorem mem_range_restrictInclusion_realizationMap (x : Realization K) :
    x ∈ range (K.restrictInclusion s).realizationMap ↔ (x.1.support : Set ι) ⊆ s := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← restrictRealizationHomeomorph_apply]
    exact (K.restrictRealizationHomeomorph s y).2
  · intro hx
    refine ⟨(K.restrictRealizationHomeomorph s).symm ⟨x, hx⟩, ?_⟩
    rw [← restrictRealizationHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- Every continuous map out of a compact space factors continuously through a finite vertex
restriction. The statement includes empty domains and imposes no hypothesis on the vertices. -/
theorem exists_finite_restrict_factorization {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, Realization K)) :
    ∃ V : Finset ι, ∃ g : C(X, Realization (K.restrict (V : Set ι))),
      (K.restrictInclusion (V : Set ι)).realizationMap.comp g = f := by
  obtain ⟨V, hV⟩ := exists_finset_support_subset_of_isCompact (isCompact_range f.continuous)
  let e := K.restrictRealizationHomeomorph (V : Set ι)
  let h : C(X, {x : Realization K // (x.1.support : Set ι) ⊆ (V : Set ι)}) :=
    ⟨fun x => ⟨f x, hV (f x) (mem_range_self x)⟩,
      f.continuous.subtype_mk (fun x => hV (f x) (mem_range_self x))⟩
  refine ⟨V, ⟨fun x => e.symm (h x), e.symm.continuous.comp h.continuous⟩, ?_⟩
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [← restrictRealizationHomeomorph_apply]
  exact congrArg Subtype.val (e.apply_symm_apply (h x))

end AbstractSimplicialComplex
