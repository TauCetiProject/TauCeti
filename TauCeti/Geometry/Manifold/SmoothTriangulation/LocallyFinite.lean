/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.LocallyCompact
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Triangulations of finite-dimensional manifolds are locally finite

If `κ : |K| ≃ₜ M` is a homeomorphism from the realization of a simplicial complex onto a
manifold modelled on a finite-dimensional space over a locally compact field (such as `ℝ`, `ℂ` or
the `p`-adic numbers), for instance a `C¹` smooth triangulation
(`TauCeti.IsSmoothTriangulation`), then `K` is locally finite: every vertex lies in finitely many
faces, and every compact subset of `M` meets `κ(σ)` for only finitely many closed simplices `σ`.
Only the homeomorphism is used. `M` is locally compact
(`Manifold.locallyCompact_of_finiteDimensional`), and the realization of a complex is locally
compact only if its vertex stars are finite
(`AbstractSimplicialComplex.finite_setOf_mem_of_weaklyLocallyCompactSpace`).
-/

public section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {K : AbstractSimplicialComplex ι}
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If the realization of `K` is homeomorphic to a manifold modelled on a finite-dimensional space
over a locally compact field, then every vertex of `K` lies in only finitely many faces. -/
theorem finite_setOf_mem_of_homeomorph_manifold (I : ModelWithCorners 𝕜 E H)
    (κ : Realization K ≃ₜ M) (v : ι) : {σ : Finset ι | σ ∈ K ∧ v ∈ σ}.Finite :=
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  finite_setOf_mem_of_homeomorph κ v

/-- If the realization of `K` is homeomorphic to a manifold modelled on a finite-dimensional space
over a locally compact field, then every compact subset of the manifold meets the images of only
finitely many closed simplices. -/
theorem finite_setOf_image_range_faceInclusion_inter_nonempty_of_manifold
    (I : ModelWithCorners 𝕜 E H) (κ : Realization K ≃ₜ M) {s : Set M} (hs : IsCompact s) :
    {σ : Face K | (κ '' range (faceInclusion K σ) ∩ s).Nonempty}.Finite :=
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  finite_setOf_image_range_faceInclusion_inter_nonempty κ hs

end AbstractSimplicialComplex
