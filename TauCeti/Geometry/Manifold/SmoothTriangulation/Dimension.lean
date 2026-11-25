/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Dimension

/-!
# Smooth triangulations have no simplices above the dimension of the manifold

A `Cⁿ` immersion of a closed simplex with vertex set `σ` into a manifold modelled on a
finite-dimensional real space `E` has, at each point, a derivative that is injective on the
directions of the simplex, the vectors of `σ → ℝ` with coordinate sum zero. These form a subspace
of dimension `|σ| - 1`, so `|σ| ≤ dim E + 1` (`TauCeti.IsSimplexImmersion.card_le`). Hence a
smooth triangulation `κ : |K| ≃ₜ M` of a manifold modelled on `E` has no simplices of dimension
above `dim E` (`TauCeti.IsSmoothTriangulation.card_le`,
`TauCeti.IsSmoothTriangulation.dimension_le`).

This is the upper half of the purity statement of §6.1 ("Smooth triangulations of boundaryless
manifolds") of the QuasiregularMaps roadmap: the triangulating complex of an `n`-manifold has no
simplices of dimension above `n`.
-/

public section

open Set Function Module AbstractSimplicialComplex TauCeti.SetLike

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- The directions of the simplex on a nonempty vertex set `σ`, the vectors of `σ → ℝ` with
coordinate sum zero, form a subspace of dimension `|σ| - 1`. -/
theorem finrank_ker_sum_proj {σ : Finset ι} (hσ : σ.Nonempty) :
    finrank ℝ (LinearMap.ker (∑ a : σ, LinearMap.proj a : (σ → ℝ) →ₗ[ℝ] ℝ)) = σ.card - 1 := by
  classical
  set s : (σ → ℝ) →ₗ[ℝ] ℝ := ∑ a : σ, LinearMap.proj a
  obtain ⟨a₀, ha₀⟩ := hσ
  have hs : LinearMap.range s = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun r ↦ ⟨Pi.single ⟨a₀, ha₀⟩ r, ?_⟩
    simp [s, LinearMap.sum_apply]
  have h := s.finrank_range_add_finrank_ker
  rw [hs, finrank_top, finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  omega

/-- A `Cⁿ` immersion of the closed simplex on a nonempty vertex set `σ` into a manifold modelled on
a finite-dimensional space `E` has `|σ| ≤ dim E + 1`: the simplex has dimension at most `dim E`. -/
theorem IsSimplexImmersion.card_le {σ : Finset ι} (hσ : σ.Nonempty) {g : StandardSimplex σ → M}
    (h : IsSimplexImmersion I n g) : σ.card ≤ finrank ℝ E + 1 := by
  obtain ⟨F, -, -, hF'⟩ := isSimplexImmersion_iff.mp h
  obtain ⟨a₀, ha₀⟩ := hσ
  obtain ⟨F', -, hinj⟩ := hF' (Convexity.StdSimplex.single (⟨a₀, ha₀⟩ : σ))
  set S := LinearMap.ker (∑ a : σ, LinearMap.proj a : (σ → ℝ) →ₗ[ℝ] ℝ)
  have hS : Injective ((F' : (σ → ℝ) →ₗ[ℝ] E).domRestrict S) := by
    refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ Subtype.ext (hinj v ?_ ?_)
    · have := v.property
      simpa [S, LinearMap.sum_apply] using this
    · simpa using hv
  have := LinearMap.finrank_le_finrank_of_injective hS
  rw [finrank_ker_sum_proj ⟨a₀, ha₀⟩] at this
  omega

/-- Every face of a smooth triangulation of a manifold modelled on a finite-dimensional space `E`
has at most `dim E + 1` vertices. -/
theorem IsSmoothTriangulation.card_le {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M}
    (h : IsSmoothTriangulation I n κ) {σ : Finset ι} (hσ : σ ∈ K) : σ.card ≤ finrank ℝ E + 1 :=
  (isSmoothTriangulation_iff.mp h ⟨σ, hσ⟩).card_le (K.isRelLowerSet_faces.prop_of_mem hσ)

/-- A smooth triangulation of a manifold modelled on a finite-dimensional space `E` has dimension
at most `dim E`: it has no simplices of dimension above that of the manifold. -/
theorem IsSmoothTriangulation.dimension_le {K : AbstractSimplicialComplex ι}
    {κ : Realization K ≃ₜ M} (h : IsSmoothTriangulation I n κ) :
    K.dimension ≤ (finrank ℝ E : WithBot ℕ∞) := by
  refine dimension_le_iff.mpr fun σ hσ ↦ ?_
  have := h.card_le hσ
  exact_mod_cast (by omega : σ.card - 1 ≤ finrank ℝ E)

end TauCeti
