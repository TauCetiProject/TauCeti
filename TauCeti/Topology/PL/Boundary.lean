/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Structure
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.HalfSpaceBoundary
public import TauCeti.Geometry.Manifold.Boundary.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Restriction

/-!
# Topological invariance of the boundary of a PL manifold

Using the boundary characterization on the realization of a positive-dimensional combinatorial
manifold (`HalfSpaceBoundary`) and homeomorphism invariance of manifold boundary and interior
(`Geometry.Manifold.Boundary.Homeomorph`), we show that for any `(n + 1)`-dimensional PL structure
`s : PLStructure M (n + 1)`:

* Relative to any finite-dimensional model with corners `I` of dimension `n + 1` on `M`, the
  manifold boundary `I.boundary M` corresponds under `s.e` to the points of `Realization s.K`
  whose support belongs to `manifoldBoundary s.K.toPreAbstractSimplicialComplex`, and `M` is
  boundaryless iff `manifoldBoundary s.K.toPreAbstractSimplicialComplex = ⊥`.
* Restricting `manifoldBoundary s.K.toPreAbstractSimplicialComplex` to its boundary vertices endows
  `I.boundary M` with a canonical `n`-dimensional PL structure `PLStructure.boundary` whose own
  combinatorial boundary is empty (`⊥`).
* Even without any `ChartedSpace` instance on `M` or `N`, any homeomorphism `M ≃ₜ N` carrying
  `s : PLStructure M (n + 1)` and `t : PLStructure N (n + 1)` respects the combinatorial boundary
  subpolyhedra and preserves emptiness of the combinatorial boundary.

## Main definitions

* `TauCeti.PLStructure.boundary`: the induced `n`-dimensional PL structure on `I.boundary M`
  obtained from an `(n + 1)`-dimensional PL structure on `M`.

## Main results

* `TauCeti.PLStructure.isBoundaryPoint_iff` and `TauCeti.PLStructure.isInteriorPoint_iff`
* `TauCeti.PLStructure.preimage_boundary`, `TauCeti.PLStructure.image_boundary`, and
  `TauCeti.PLStructure.image_manifoldInterior`
* `TauCeti.PLStructure.boundary_eq_empty_iff` and `TauCeti.PLStructure.boundarylessManifold_iff`
* `TauCeti.PLStructure.manifoldBoundary_boundary_eq_bot`
* `TauCeti.PLStructure.image_manifoldBoundary_of_homeomorph` and
  `TauCeti.PLStructure.manifoldBoundary_eq_bot_iff_of_homeomorph`
-/

public section

noncomputable section

open AbstractSimplicialComplex PreAbstractSimplicialComplex Set Module
open scoped Manifold

namespace TauCeti.PLStructure

attribute [local instance] Classical.decEq

section ChartedBoundary

variable {M : Type u} [TopologicalSpace M] {n : ℕ} (s : PLStructure M (n + 1))
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H M]

/-- For any `(n + 1)`-dimensional PL structure on a charted space `M` modelled on a space of real
dimension `n + 1`, a point lies on the manifold boundary iff its barycentric support lies in
`manifoldBoundary`. -/
theorem isBoundaryPoint_iff (hE : finrank ℝ E = n + 1) (x : M) :
    I.IsBoundaryPoint x ↔
      (s.e.symm x).val.support ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex := by
  let := s.isCombinatorialManifold.realizationChartedSpace
  have hdim : finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by simp [hE]
  rw [s.e.symm.isBoundaryPoint_iff I (𝓡∂ (n + 1)) hdim x]
  exact s.isCombinatorialManifold.isBoundaryPoint_realizationChartedSpace_iff (s.e.symm x)

/-- For any `(n + 1)`-dimensional PL structure on a charted space `M` modelled on a space of real
dimension `n + 1`, a point lies in the manifold interior iff its barycentric support avoids
`manifoldBoundary`. -/
theorem isInteriorPoint_iff (hE : finrank ℝ E = n + 1) (x : M) :
    I.IsInteriorPoint x ↔
      (s.e.symm x).val.support ∉ manifoldBoundary s.K.toPreAbstractSimplicialComplex := by
  rw [I.isInteriorPoint_iff_not_isBoundaryPoint]
  exact not_congr (s.isBoundaryPoint_iff I hE x)

/-- The preimage of `I.boundary M` in `Realization s.K` under `s.e` is the subpolyhedron spanned
by `manifoldBoundary`. -/
theorem preimage_boundary (hE : finrank ℝ E = n + 1) :
    s.e ⁻¹' I.boundary M =
      {x : Realization s.K |
        x.val.support ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex} := by
  ext x
  change I.IsBoundaryPoint (s.e x) ↔ _
  simpa using s.isBoundaryPoint_iff I hE (s.e x)

/-- `I.boundary M` is the `s.e`-image of the combinatorial boundary subpolyhedron. -/
theorem image_boundary (hE : finrank ℝ E = n + 1) :
    s.e '' {x : Realization s.K |
      x.val.support ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex} = I.boundary M :=
  (s.e.eq_preimage_iff_image_eq _ _).1 (s.preimage_boundary I hE).symm

/-- `I.interior M` is the `s.e`-image of the complement of the combinatorial boundary
subpolyhedron. -/
theorem image_manifoldInterior (hE : finrank ℝ E = n + 1) :
    s.e '' {x : Realization s.K |
      x.val.support ∉ manifoldBoundary s.K.toPreAbstractSimplicialComplex} = I.interior M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (s.isInteriorPoint_iff I hE (s.e y)).mpr (by simpa using hy)
  · intro hx
    refine ⟨s.e.symm x, ?_, s.e.apply_symm_apply x⟩
    exact (s.isInteriorPoint_iff I hE x).mp hx

/-- The manifold boundary of `M` is empty iff the combinatorial boundary of `s.K` is `⊥`. -/
theorem boundary_eq_empty_iff (hE : finrank ℝ E = n + 1) :
    I.boundary M = ∅ ↔ manifoldBoundary s.K.toPreAbstractSimplicialComplex = ⊥ := by
  rw [← s.image_boundary I hE, image_eq_empty, eq_empty_iff_forall_notMem]
  constructor
  · intro h
    refine SetLike.ext fun σ => ⟨fun hσ => ?_, fun hσ => False.elim (notMem_bot hσ)⟩
    obtain ⟨x, hx⟩ := AbstractSimplicialComplex.exists_support_eq (manifoldBoundary_le hσ)
    exact False.elim (h x (by simpa [hx] using hσ))
  · intro hbot x hx
    simp only [Set.mem_ofPred_eq, hbot] at hx
    exact notMem_bot hx

/-- `M` is a boundaryless manifold iff the combinatorial boundary of `s.K` is `⊥`. -/
theorem boundarylessManifold_iff (hE : finrank ℝ E = n + 1) :
    BoundarylessManifold I M ↔ manifoldBoundary s.K.toPreAbstractSimplicialComplex = ⊥ := by
  rw [← ModelWithCorners.Boundaryless.iff_boundary_eq_empty]
  exact s.boundary_eq_empty_iff I hE

private def boundaryComplex {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) :
    AbstractSimplicialComplex
      {v : ι // ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex} :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex _
    ((manifoldBoundary K.toPreAbstractSimplicialComplex).restrict
      {v : ι | ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex})
    fun v => by
      rw [mem_faces, mem_restrict_iff_map, Finset.map_singleton]
      exact v.property

private theorem map_boundaryComplex {ι : Type u} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) :
    (boundaryComplex K).toPreAbstractSimplicialComplex.map
        (Function.Embedding.subtype (· ∈
          {v : ι | ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex})) =
      manifoldBoundary K.toPreAbstractSimplicialComplex := by
  refine PreAbstractSimplicialComplex.ext ?_
  ext σ
  change σ ∈ ((manifoldBoundary K.toPreAbstractSimplicialComplex).restrict _).map
      (Subtype.val : {v : ι |
        ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex} → ι) ↔
    σ ∈ manifoldBoundary K.toPreAbstractSimplicialComplex
  rw [PreAbstractSimplicialComplex.mem_map_restrict_iff]
  refine ⟨fun h => h.1, fun hσ => ⟨hσ, fun v hv => ?_⟩⟩
  exact (manifoldBoundary K.toPreAbstractSimplicialComplex).isRelLowerSet_faces.mem_of_le
    hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

/-- The boundary `I.boundary M` inherits an `n`-dimensional PL structure by restricting the
combinatorial boundary of `s.K` to its boundary vertices. -/
def boundary (hE : finrank ℝ E = n + 1) : PLStructure (I.boundary M) n := by
  let B := manifoldBoundary s.K.toPreAbstractSimplicialComplex
  let V : Set s.ι := {v : s.ι | ({v} : Finset s.ι) ∈ B}
  let KB := boundaryComplex s.K
  have hKBmap : KB.toPreAbstractSimplicialComplex.map Subtype.val = B :=
    map_boundaryComplex s.K
  have hKBman : IsCombinatorialManifold KB.toPreAbstractSimplicialComplex n := by
    rw [← isCombinatorialManifold_map_iff Subtype.val_injective, hKBmap]
    exact s.isCombinatorialManifold.isCombinatorialManifold_manifoldBoundary
  let r : Realization KB ≃ₜ {x : Realization s.K | x.val.support ∈ B} :=
    KB.toPreAbstractSimplicialComplex.realizationRelabelingHomeomorph
      (Function.Embedding.subtype (· ∈ V)) (map_boundaryComplex s.K) rfl
      (manifoldBoundary_le (K := s.K.toPreAbstractSimplicialComplex))
  let := s.isCombinatorialManifold.realizationChartedSpace
  have hcod : {x : Realization s.K | x.val.support ∈ B} =
      (𝓡∂ (n + 1)).boundary (Realization s.K) :=
    s.isCombinatorialManifold.boundary_realizationChartedSpace.symm
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = finrank ℝ E := by simp [hE]
  let eB : Realization KB ≃ₜ I.boundary M :=
    r.trans ((Homeomorph.setCongr hcod).trans (s.e.boundaryHomeomorph (𝓡∂ (n + 1)) I hdim))
  exact ⟨{v : s.ι // ({v} : Finset s.ι) ∈ B}, KB,
    by rw [Subsingleton.elim (Classical.decEq _) Subtype.instDecidableEq]; exact hKBman, eB⟩

/-- The induced PL structure on the boundary `I.boundary M` is itself boundaryless: its
combinatorial boundary is `⊥`. -/
theorem manifoldBoundary_boundary_eq_bot (hE : finrank ℝ E = n + 1) :
    manifoldBoundary (s.boundary I hE).K.toPreAbstractSimplicialComplex = ⊥ := by
  dsimp only [boundary]
  have hbd :
      (manifoldBoundary (boundaryComplex s.K).toPreAbstractSimplicialComplex).map
        (Subtype.val : {v : s.ι //
          ({v} : Finset s.ι) ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex} → s.ι) =
        ⊥ := by
    rw [map_manifoldBoundary _ Subtype.val_injective]
    have hmap : (boundaryComplex s.K).toPreAbstractSimplicialComplex.map Subtype.val =
        manifoldBoundary s.K.toPreAbstractSimplicialComplex :=
      map_boundaryComplex s.K
    rw [hmap]
    exact s.isCombinatorialManifold.manifoldBoundary_manifoldBoundary
  refine SetLike.ext fun σ => ⟨fun hσ => ?_, fun hσ => False.elim (notMem_bot hσ)⟩
  have hdec : (Classical.decEq {v : s.ι //
      ({v} : Finset s.ι) ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex}) =
      Subtype.instDecidableEq :=
    Subsingleton.elim _ _
  have hσ' : σ ∈ manifoldBoundary (boundaryComplex s.K).toPreAbstractSimplicialComplex := by
    change σ ∈ @manifoldBoundary _ (Classical.decEq _) _ at hσ
    rwa [hdec] at hσ
  have hmem : σ.image Subtype.val ∈
      (manifoldBoundary (boundaryComplex s.K).toPreAbstractSimplicialComplex).map
        (Subtype.val : {v : s.ι //
          ({v} : Finset s.ι) ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex} → s.ι) :=
    mem_map_iff.mpr ⟨σ, hσ', rfl⟩
  rw [hbd] at hmem
  exact False.elim (notMem_bot hmem)

end ChartedBoundary

section HomeomorphInvariance

private theorem forall_notMem_manifoldBoundary_iff {ι : Type*} [DecidableEq ι]
    (K : AbstractSimplicialComplex ι) :
    (∀ x : Realization K, x.val.support ∉ manifoldBoundary K.toPreAbstractSimplicialComplex) ↔
      manifoldBoundary K.toPreAbstractSimplicialComplex = ⊥ := by
  refine ⟨fun h => SetLike.ext fun σ =>
      ⟨fun hσ => ?_, fun hσ => False.elim (notMem_bot hσ)⟩,
    fun hbot x hx => ?_⟩
  · obtain ⟨x, hx⟩ := AbstractSimplicialComplex.exists_support_eq (manifoldBoundary_le hσ)
    exact False.elim (h x (by simpa [hx] using hσ))
  · rw [hbot] at hx
    exact notMem_bot hx

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N] {n : ℕ}
  (s : PLStructure M (n + 1)) (t : PLStructure N (n + 1))

/-- Any homeomorphism `f : M ≃ₜ N` between spaces carrying `(n + 1)`-dimensional PL structures
carries the combinatorial boundary subpolyhedron of `s` onto that of `t`, without assuming any
charted-space instances on `M` or `N`. -/
theorem image_manifoldBoundary_of_homeomorph (f : M ≃ₜ N) :
    (t.e.symm ∘ f ∘ s.e) ''
        {x : Realization s.K |
          x.val.support ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex} =
      {y : Realization t.K |
        y.val.support ∈ manifoldBoundary t.K.toPreAbstractSimplicialComplex} := by
  let := s.isCombinatorialManifold.realizationChartedSpace
  let := t.isCombinatorialManifold.realizationChartedSpace
  let g : Realization s.K ≃ₜ Realization t.K := s.e.trans (f.trans t.e.symm)
  have hg := g.image_boundary (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) rfl
  rw [s.isCombinatorialManifold.boundary_realizationChartedSpace,
    t.isCombinatorialManifold.boundary_realizationChartedSpace] at hg
  exact hg

/-- Being boundaryless combinatorially (`manifoldBoundary = ⊥`) is invariant under homeomorphism
between spaces carrying `(n + 1)`-dimensional PL structures. -/
theorem manifoldBoundary_eq_bot_iff_of_homeomorph (f : M ≃ₜ N) :
    manifoldBoundary s.K.toPreAbstractSimplicialComplex = ⊥ ↔
      manifoldBoundary t.K.toPreAbstractSimplicialComplex = ⊥ := by
  let := s.isCombinatorialManifold.realizationChartedSpace
  let := t.isCombinatorialManifold.realizationChartedSpace
  let g : Realization s.K ≃ₜ Realization t.K := s.e.trans (f.trans t.e.symm)
  have hbe : (𝓡∂ (n + 1)).boundary (Realization s.K) = ∅ ↔
      (𝓡∂ (n + 1)).boundary (Realization t.K) = ∅ :=
    g.boundary_eq_empty_iff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) rfl
  rw [s.isCombinatorialManifold.boundary_realizationChartedSpace,
    t.isCombinatorialManifold.boundary_realizationChartedSpace,
    eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem] at hbe
  simp only [Set.mem_ofPred_eq, forall_notMem_manifoldBoundary_iff] at hbe
  exact hbe

end HomeomorphInvariance

end TauCeti.PLStructure
