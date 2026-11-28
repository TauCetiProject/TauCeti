/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Structure
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.HalfSpaceBoundary
public import TauCeti.Geometry.Manifold.Boundary.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction

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
* `TauCeti.PLStructure.boundary_ι`, `TauCeti.PLStructure.boundary_K`, and
  `TauCeti.PLStructure.coe_boundary_e`
* `TauCeti.PLStructure.manifoldBoundary_boundary_eq_bot`
* `TauCeti.PLStructure.image_manifoldBoundary_of_homeomorph` and
  `TauCeti.PLStructure.manifoldBoundary_eq_bot_iff_of_homeomorph`

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2–3 (boundary of a PL manifold and closedness of the boundary).
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
  let := s.isCombinatorialManifold.realizationChartedSpace
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = finrank ℝ E := by simp [hE]
  rw [s.e.preimage_boundary (𝓡∂ (n + 1)) I hdim]
  exact s.isCombinatorialManifold.boundary_realizationChartedSpace

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
  let := s.isCombinatorialManifold.realizationChartedSpace
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = finrank ℝ E := by simp [hE]
  rw [← s.isCombinatorialManifold.interior_realizationChartedSpace]
  exact s.e.image_manifoldInterior (𝓡∂ (n + 1)) I hdim

/-- The manifold boundary of `M` is empty iff the combinatorial boundary of `s.K` is `⊥`. -/
theorem boundary_eq_empty_iff (hE : finrank ℝ E = n + 1) :
    I.boundary M = ∅ ↔ manifoldBoundary s.K.toPreAbstractSimplicialComplex = ⊥ := by
  rw [← s.image_boundary I hE, image_eq_empty, eq_empty_iff_forall_notMem]
  exact AbstractSimplicialComplex.forall_support_notMem_iff_eq_bot manifoldBoundary_le

/-- `M` is a boundaryless manifold iff the combinatorial boundary of `s.K` is `⊥`. -/
theorem boundarylessManifold_iff (hE : finrank ℝ E = n + 1) :
    BoundarylessManifold I M ↔ manifoldBoundary s.K.toPreAbstractSimplicialComplex = ⊥ := by
  rw [← ModelWithCorners.Boundaryless.iff_boundary_eq_empty]
  exact s.boundary_eq_empty_iff I hE

/-- The boundary `I.boundary M` inherits an `n`-dimensional PL structure by restricting the
combinatorial boundary of `s.K` to its boundary vertices. The body is exposed so that the
vertex type and triangulating complex of `s.boundary I hE` are given by `restrictToVertices`
definitionally. -/
@[expose] def boundary (hE : finrank ℝ E = n + 1) : PLStructure (I.boundary M) n where
  ι := {v : s.ι // ({v} : Finset s.ι) ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex}
  K := (manifoldBoundary s.K.toPreAbstractSimplicialComplex).restrictToVertices
  isCombinatorialManifold := by
    rw [isCombinatorialManifold_congr_decidableEq (Classical.decEq _) Subtype.instDecidableEq,
      ← isCombinatorialManifold_map_iff Subtype.val_injective, map_val_restrictToVertices]
    exact s.isCombinatorialManifold.isCombinatorialManifold_manifoldBoundary
  e :=
    let := s.isCombinatorialManifold.realizationChartedSpace
    (restrictToVerticesRealizationHomeomorph
      (K := s.K) (manifoldBoundary_le (K := s.K.toPreAbstractSimplicialComplex))).trans
      ((Homeomorph.setCongr s.isCombinatorialManifold.boundary_realizationChartedSpace.symm).trans
        (s.e.boundaryHomeomorph (𝓡∂ (n + 1)) I (by simp [hE])))

/-- The vertex type of `s.boundary I hE` consists of the boundary vertices of `s.K`. -/
@[simp]
theorem boundary_ι (hE : finrank ℝ E = n + 1) :
    (s.boundary I hE).ι =
      {v : s.ι // ({v} : Finset s.ι) ∈ manifoldBoundary s.K.toPreAbstractSimplicialComplex} :=
  (rfl)

/-- The triangulating complex of `s.boundary I hE` is the vertex restriction of the combinatorial
boundary of `s.K`. -/
@[simp]
theorem boundary_K (hE : finrank ℝ E = n + 1) :
    (s.boundary I hE).K =
      (manifoldBoundary s.K.toPreAbstractSimplicialComplex).restrictToVertices :=
  (rfl)

/-- On underlying points of `M`, the triangulation homeomorphism of `s.boundary I hE` pushes
barycentric coordinates forward along `Subtype.val` and applies `s.e`. -/
@[simp]
theorem coe_boundary_e (hE : finrank ℝ E = n + 1)
    (y : Realization (s.boundary I hE).K) :
    ((s.boundary I hE).e y : M) =
      s.e ⟨Finsupp.mapDomain Subtype.val y.val, by
        rw [← restrictToVerticesRealizationHomeomorph_val
          (manifoldBoundary_le (K := s.K.toPreAbstractSimplicialComplex)) y]
        exact (restrictToVerticesRealizationHomeomorph (K := s.K)
          (manifoldBoundary_le (K := s.K.toPreAbstractSimplicialComplex)) y).val.property⟩ :=
  let := s.isCombinatorialManifold.realizationChartedSpace
  (Homeomorph.coe_boundaryHomeomorph_apply _ _ _ _ _).trans <|
    congrArg s.e <| Subtype.ext <| restrictToVerticesRealizationHomeomorph_val
      (manifoldBoundary_le (K := s.K.toPreAbstractSimplicialComplex)) y

/-- The induced PL structure on the boundary `I.boundary M` is itself boundaryless: its
combinatorial boundary is `⊥`. -/
theorem manifoldBoundary_boundary_eq_bot (hE : finrank ℝ E = n + 1) :
    manifoldBoundary (s.boundary I hE).K.toPreAbstractSimplicialComplex = ⊥ := by
  let B := (manifoldBoundary s.K.toPreAbstractSimplicialComplex).restrictToVertices
  have hmb :
      manifoldBoundary (s.boundary I hE).K.toPreAbstractSimplicialComplex =
        @manifoldBoundary _ Subtype.instDecidableEq B.toPreAbstractSimplicialComplex :=
    manifoldBoundary_congr_decidableEq
      (K := B.toPreAbstractSimplicialComplex) (Classical.decEq _) Subtype.instDecidableEq
  have hbot :
      @manifoldBoundary _ Subtype.instDecidableEq B.toPreAbstractSimplicialComplex = ⊥ := by
    apply map_injective Subtype.val_injective
    dsimp only
    rw [map_manifoldBoundary _ Subtype.val_injective, map_val_restrictToVertices,
      PreAbstractSimplicialComplex.map_bot]
    exact s.isCombinatorialManifold.manifoldBoundary_manifoldBoundary
  exact hmb.trans hbot

end ChartedBoundary

section HomeomorphInvariance

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
  simp only [Set.mem_ofPred_eq,
    AbstractSimplicialComplex.forall_support_notMem_iff_eq_bot manifoldBoundary_le] at hbe
  exact hbe

end HomeomorphInvariance

end TauCeti.PLStructure
