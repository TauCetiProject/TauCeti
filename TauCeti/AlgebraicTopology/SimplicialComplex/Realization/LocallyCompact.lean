/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.LocallyFinite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Compact
public import Mathlib.Topology.UnitInterval

/-!
# Locally compact realizations are locally finite

A weak realization `|K|` whose vertex stars are finite is locally compact
(`AbstractSimplicialComplex.locallyCompactSpace_realization_of_finite_vertex_stars`). This file
proves the converse: if `|K|` is weakly locally compact then every vertex, and hence every face,
of `K` lies in only finitely many faces, and every compact subset of `|K|` meets only finitely many
closed simplices. So a complex whose realization is homeomorphic to a locally compact space, for
instance a finite-dimensional manifold, is locally finite.

The proof follows the segment from a vertex `v` to the barycentre of a face `σ ∋ v`: its points
other than `v` have carrier `σ`, and they come arbitrarily close to `v`. A compact neighbourhood of
`v` uses only finitely many vertices
(`AbstractSimplicialComplex.exists_finset_support_subset_of_isCompact`), so every face
containing `v` is a subset of one finite vertex set.

Local compactness is needed: the infinite star, a vertex joined to infinitely many others, is not
locally finite.

## Main results

* `AbstractSimplicialComplex.finite_setOf_mem_of_weaklyLocallyCompactSpace`: a vertex lies in
  finitely many faces.
* `AbstractSimplicialComplex.finite_setOf_subset_of_weaklyLocallyCompactSpace`: a face is a face
  of finitely many faces.
* `AbstractSimplicialComplex.locallyCompactSpace_realization_iff`: `|K|` is locally compact if and
  only if every closed vertex star is finite.
* `AbstractSimplicialComplex.finite_setOf_range_faceInclusion_inter_nonempty`: a compact subset of
  a locally compact realization meets finitely many closed simplices.
* `AbstractSimplicialComplex.finite_setOf_mem_of_homeomorph`,
  `AbstractSimplicialComplex.finite_setOf_image_range_faceInclusion_inter_nonempty`: the same for
  a homeomorphism `|K| ≃ₜ X` onto a locally compact space, with the images of the closed
  simplices.
-/

public section

noncomputable section

open Set Filter Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {K : AbstractSimplicialComplex ι}

attribute [local instance] Classical.decEq

/-- If every point of a neighbourhood `C` of the realization vertex `v` has support in `V`, then
every face containing `v` is contained in `V`. -/
theorem subset_of_mem_nhds_vertex {v : ι} {C : Set (Realization K)} (hC : C ∈ 𝓝 (vertex K v))
    {V : Finset ι} (hV : ∀ x ∈ C, x.val.support ⊆ V) {σ : Finset ι} (hσ : σ ∈ K) (hv : v ∈ σ) :
    σ ⊆ V := by
  let e : StandardSimplex σ := ⟨Finsupp.single v 1, subset_convexHull ℝ _
    (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, rfl⟩))⟩
  let b : StandardSimplex σ := ⟨faceBarycenter K ⟨σ, hσ⟩, faceBarycenter_mem K ⟨σ, hσ⟩⟩
  let p : unitInterval → Realization K := fun t ↦ faceInclusion K ⟨σ, hσ⟩
    (StandardSimplex.lineMap e b t)
  have hp : Continuous p :=
    (continuous_faceInclusion K _).comp (StandardSimplex.continuous_lineMap e b)
  have hp0 : p 0 = vertex K v := Subtype.ext (by simp [p, e])
  have hpre : p ⁻¹' C ∈ 𝓝 (0 : unitInterval) := hp.continuousAt.preimage_mem_nhds (hp0 ▸ hC)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let t : unitInterval := ⟨min (ε / 2) 1, le_min (by positivity) zero_le_one,
    min_le_right _ _⟩
  have ht0 : 0 < (t : ℝ) := lt_min (by positivity) one_pos
  have htε : (t : ℝ) < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have htC : p t ∈ C := hball (by simpa [Subtype.dist_eq, Real.dist_eq, abs_of_pos ht0] using htε)
  intro w hw
  refine hV _ htC (Finsupp.mem_support_iff.mpr (ne_of_gt ?_))
  have hcard : (0 : ℝ) < σ.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨w, hw⟩)
  have h1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  simp only [p, faceInclusion_val, StandardSimplex.lineMap_apply, e, b, faceBarycenter_apply, hw,
    ite_true]
  have : 0 ≤ (Finsupp.single v (1 : ℝ)) w := Finsupp.single_nonneg.mpr zero_le_one w
  positivity

/-- In a weakly locally compact realization, a vertex lies in only finitely many faces. -/
theorem finite_setOf_mem_of_weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace (Realization K)]
    (v : ι) : {σ : Finset ι | σ ∈ K ∧ v ∈ σ}.Finite := by
  obtain ⟨C, hCc, hC⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds (vertex K v)
  obtain ⟨V, hV⟩ := exists_finset_support_subset_of_isCompact hCc
  refine ((V.powerset : Set (Finset ι)).toFinite).subset fun σ hσ ↦ ?_
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (subset_of_mem_nhds_vertex hC hV hσ.1 hσ.2))

/-- In a weakly locally compact realization, a nonempty finite set of vertices (for instance a
face) is contained in only finitely many faces. -/
theorem finite_setOf_subset_of_weaklyLocallyCompactSpace
    [WeaklyLocallyCompactSpace (Realization K)] {τ : Finset ι} (hτ : τ.Nonempty) :
    {σ : Finset ι | σ ∈ K ∧ τ ⊆ σ}.Finite := by
  obtain ⟨v, hv⟩ := hτ
  exact (finite_setOf_mem_of_weaklyLocallyCompactSpace v).subset fun σ hσ ↦ ⟨hσ.1, hσ.2 hv⟩

/-- In a weakly locally compact realization, every closed vertex star is finite. -/
theorem finite_faces_closedStar_of_weaklyLocallyCompactSpace [DecidableEq ι]
    [WeaklyLocallyCompactSpace (Realization K)] (v : ι) :
    (PreAbstractSimplicialComplex.closedStar
      K.toPreAbstractSimplicialComplex {v}).faces.Finite := by
  refine ((finite_setOf_mem_of_weaklyLocallyCompactSpace (K := K) v).biUnion
    fun σ _ ↦ (σ.powerset : Set (Finset ι)).toFinite).subset fun ρ hρ ↦ ?_
  have hρK : ρ ∪ {v} ∈ K := (PreAbstractSimplicialComplex.mem_closedStar_nonempty.mp hρ).2
  exact mem_biUnion (x := ρ ∪ {v}) ⟨hρK, Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩
    (Finset.mem_coe.mpr (Finset.mem_powerset.mpr Finset.subset_union_left))

/-- A weak realization is locally compact if and only if every closed vertex star is finite. -/
theorem locallyCompactSpace_realization_iff [DecidableEq ι] :
    LocallyCompactSpace (Realization K) ↔ ∀ v : ι,
      (PreAbstractSimplicialComplex.closedStar K.toPreAbstractSimplicialComplex {v}).faces.Finite :=
  ⟨fun _ ↦ finite_faces_closedStar_of_weaklyLocallyCompactSpace,
    K.locallyCompactSpace_realization_of_finite_vertex_stars⟩

/-- In a weakly locally compact realization, a compact set meets only finitely many closed
simplices. -/
theorem finite_setOf_range_faceInclusion_inter_nonempty
    [WeaklyLocallyCompactSpace (Realization K)] {s : Set (Realization K)} (hs : IsCompact s) :
    {σ : Face K | (range (faceInclusion K σ) ∩ s).Nonempty}.Finite := by
  obtain ⟨V, hV⟩ := exists_finset_support_subset_of_isCompact hs
  have hfin : {σ : Finset ι | σ ∈ K ∧ ∃ w ∈ V, w ∈ σ}.Finite := by
    refine ((V.finite_toSet.biUnion fun w _ ↦
      finite_setOf_mem_of_weaklyLocallyCompactSpace (K := K) w)).subset ?_
    rintro σ ⟨hσ, w, hwV, hwσ⟩
    exact mem_biUnion hwV ⟨hσ, hwσ⟩
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro σ ⟨_, ⟨y, rfl⟩, hys⟩
  obtain ⟨w, hw⟩ := K.isRelLowerSet_faces.prop_of_mem (support_mem K (faceInclusion K σ y))
  refine ⟨σ.property, w, hV _ hys hw, ?_⟩
  rw [faceInclusion_val] at hw
  exact StandardSimplex.support_subset y hw

/-- If `|K|` is homeomorphic to a weakly locally compact space, for instance a finite-dimensional
manifold, then every vertex lies in only finitely many faces. -/
theorem finite_setOf_mem_of_homeomorph {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] (κ : Realization K ≃ₜ X) (v : ι) :
    {σ : Finset ι | σ ∈ K ∧ v ∈ σ}.Finite :=
  have : WeaklyLocallyCompactSpace (Realization K) :=
    κ.isClosedEmbedding.weaklyLocallyCompactSpace
  finite_setOf_mem_of_weaklyLocallyCompactSpace v

/-- If `κ : |K| ≃ₜ X` is a homeomorphism onto a weakly locally compact space, for instance a
finite-dimensional manifold, then every compact subset of `X` meets the images of only finitely
many closed simplices. -/
theorem finite_setOf_image_range_faceInclusion_inter_nonempty {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] (κ : Realization K ≃ₜ X) {s : Set X} (hs : IsCompact s) :
    {σ : Face K | (κ '' range (faceInclusion K σ) ∩ s).Nonempty}.Finite := by
  have : WeaklyLocallyCompactSpace (Realization K) :=
    κ.isClosedEmbedding.weaklyLocallyCompactSpace
  refine (finite_setOf_range_faceInclusion_inter_nonempty
    (hs.image κ.symm.continuous)).subset fun σ ⟨_, ⟨x, hx, rfl⟩, hxs⟩ ↦ ?_
  exact ⟨x, hx, κ x, hxs, κ.symm_apply_apply x⟩

end AbstractSimplicialComplex
