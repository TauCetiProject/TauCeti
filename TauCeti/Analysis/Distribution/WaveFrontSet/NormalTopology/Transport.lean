/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
public import TauCeti.Analysis.Distribution.WaveFrontSet.Transport

/-!
# Transport along linear isometries in the normal topology

Let `L : E' ≃ₗᵢ[ℝ] E` be a linear isometry of finite-dimensional real inner product spaces
identifying an open set `Ω'` of `E'` with an open set `Ω` of `E`, and let `Γ` be a subset of
`E × E`. The transport `L^* T = φ ↦ T (φ ∘ L⁻¹)` of distributions (`Distribution.transportCLM`)
moves wave front sets by `L⁻¹` in positions and covectors
(`Distribution.waveFrontSet_transportCLM`), so it maps `𝓓'_Γ(Ω)` to `𝓓'_{L^* Γ}(Ω')`, where
`L^* Γ = {(x, ξ) | (L x, L ξ) ∈ Γ}`. This file proves that it is continuous for the normal
topologies (`TauCeti.WaveFrontSpace.transportCLM`): each seminorm of `L^* T` is a seminorm of
`T` with transported data, `‖L^* T‖_{φ,V,N} = ‖T‖_{φ ∘ L⁻¹, L V, N}`
(`TauCeti.WaveFrontSpace.seminorm_transportCLM`), since the localized Fourier transform of `L^* T`
at `η` is that of `T` at `L η` and `‖L η‖ = ‖η‖` (`Distribution.localFourier_transportCLM`).

This moves spaces of distributions with prescribed wave front set between different Euclidean
spaces, for instance between the Euclidean products `WithLp 2 (E × D)` and `WithLp 2 (D × E)`.

## Main declarations

* `TauCeti.WaveFrontSeminormIndex.transport`: the data `(φ ∘ L⁻¹, L V, N)` of a seminorm of
  `𝓓'_Γ(Ω)` from the data `(φ, V, N)` of a seminorm of `𝓓'_{L^* Γ}(Ω')`.
* `TauCeti.WaveFrontSpace.transportCLM`: the transport `L^* : 𝓓'_Γ(Ω) →L[ℂ] 𝓓'_{L^* Γ}(Ω')`.
* `TauCeti.WaveFrontSpace.seminorm_transportCLM`: `‖L^* T‖_{φ,V,N} = ‖T‖_{φ ∘ L⁻¹, L V, N}`.

## References

* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, §3 (the normal topology and its seminorms).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction
open scoped Distributions

namespace TauCeti

open Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'}
  {Γ : Set (E × E)}

namespace WaveFrontSeminormIndex

/-- The data `(φ ∘ L⁻¹, L V, N)` of a seminorm of `𝓓'_Γ(Ω)` transported along the linear isometry
`L` from the data `i = (φ, V, N)` of a seminorm of `𝓓'_{L^* Γ}(Ω')`, where
`L^* Γ = {(x, ξ) | (L x, L ξ) ∈ Γ}`. -/
def transport (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (i : WaveFrontSeminormIndex Ω' (Prod.map L L ⁻¹' Γ)) : WaveFrontSeminormIndex Ω Γ where
  cutoff := L.toContinuousLinearEquiv.transportTestFunction ℝ h i.cutoff
  cone := L.symm ⁻¹' i.cone
  order := i.order
  isClosed_cone := i.isClosed_cone.preimage L.symm.continuous
  smul_mem_cone t ht η hη := by
    simpa only [mem_preimage, map_smul] using i.smul_mem_cone t ht _ hη
  disjoint := by
    refine disjoint_left.2 fun p hp hpΓ ↦ ?_
    -- The point `(L⁻¹ p.1, L⁻¹ p.2)` lies over the support of `φ` in a direction of `V`, and in
    -- `L^* Γ`.
    have hcoe : ⇑(L.toContinuousLinearEquiv.transportTestFunction ℝ h i.cutoff) =
        i.cutoff ∘ L.symm := by
      ext
      simp
    have h₁ : L.symm p.1 ∈ tsupport i.cutoff :=
      tsupport_comp_subset_preimage _ L.symm.continuous (hcoe ▸ hp.1)
    exact disjoint_left.1 i.disjoint (mk_mem_prod h₁ hp.2) (by simpa using hpΓ)

@[simp]
theorem transport_cutoff (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (i : WaveFrontSeminormIndex Ω' (Prod.map L L ⁻¹' Γ)) :
    (i.transport L h).cutoff = L.toContinuousLinearEquiv.transportTestFunction ℝ h i.cutoff :=
  (rfl)

@[simp]
theorem transport_cone (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (i : WaveFrontSeminormIndex Ω' (Prod.map L L ⁻¹' Γ)) :
    (i.transport L h).cone = L.symm ⁻¹' i.cone :=
  (rfl)

@[simp]
theorem transport_order (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (i : WaveFrontSeminormIndex Ω' (Prod.map L L ⁻¹' Γ)) : (i.transport L h).order = i.order :=
  (rfl)

end WaveFrontSeminormIndex

namespace WaveFrontSpace

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- The transport `L^* : 𝓓'_Γ(Ω) → 𝓓'_{L^* Γ}(Ω')` as a linear map, before its continuity is
proved. -/
private def transportₗ (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω') :
    WaveFrontSpace Ω Γ →ₗ[ℂ] WaveFrontSpace Ω' (Prod.map L L ⁻¹' Γ) where
  toFun u := mk (Distribution.transportCLM L.toContinuousLinearEquiv h u.toDistribution) <| by
    rw [waveFrontSet_transportCLM L h h']
    exact preimage_mono u.waveFrontSet_toDistribution_subset
  map_add' u v := ext (by simp)
  map_smul' c u := ext (by ext φ; simp)

private theorem toDistribution_transportₗ (L : E' ≃ₗᵢ[ℝ] E)
    (h : MapsTo L.toContinuousLinearEquiv Ω' Ω) (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω')
    (u : WaveFrontSpace Ω Γ) :
    (transportₗ L h h' u).toDistribution =
      Distribution.transportCLM L.toContinuousLinearEquiv h u.toDistribution :=
  toDistribution_mk _ _

private theorem seminorm_transportₗ (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω')
    (i : WaveFrontSeminormIndex Ω' (Prod.map L L ⁻¹' Γ)) (u : WaveFrontSpace Ω Γ) :
    WaveFrontSpace.seminorm i (transportₗ L h h' u) =
      WaveFrontSpace.seminorm (i.transport L h) u := by
  -- The localized Fourier transform of `L^* u` at `η` is that of `u` at `L η`, and `L` maps `V`
  -- onto `L V` preserving norms.
  refine le_antisymm (seminorm_le_bound i _ (apply_nonneg _ _) fun η hη ↦ ?_)
    (seminorm_le_bound _ u (apply_nonneg _ _) fun ζ hζ ↦ ?_)
  · have hle := le_seminorm (i.transport L h) u (η := L η) (by simpa using hη)
    rwa [WaveFrontSeminormIndex.transport_order, WaveFrontSeminormIndex.transport_cutoff,
      LinearIsometryEquiv.norm_map, ← Distribution.localFourier_transportCLM,
      ← toDistribution_transportₗ L h h'] at hle
  · have hle := le_seminorm i (transportₗ L h h' u) (η := L.symm ζ) hζ
    rwa [toDistribution_transportₗ, Distribution.localFourier_transportCLM,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] at hle

/-- **Transport along a linear isometry in the normal topology.** Let `L : E' ≃ₗᵢ[ℝ] E` identify
`Ω'` with `Ω`. The transport `L^* T = φ ↦ T (φ ∘ L⁻¹)` (`Distribution.transportCLM`) is a
continuous linear map from `𝓓'_Γ(Ω)` to `𝓓'_{L^* Γ}(Ω')`, where
`L^* Γ = {(x, ξ) | (L x, L ξ) ∈ Γ}`. -/
def transportCLM (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω') :
    WaveFrontSpace Ω Γ →L[ℂ] WaveFrontSpace Ω' (Prod.map L L ⁻¹' Γ) :=
  ⟨transportₗ L h h', by
    refine continuous_linearMap_of_le _ ?_ fun i ↦ ⟨WaveFrontSpace.seminorm (i.transport L h),
      continuous_seminorm _, fun u ↦ (seminorm_transportₗ L h h' i u).le⟩
    have hcomp : ⇑(toDistribution ∘ₗ transportₗ (Γ := Γ) L h h') =
        Distribution.transportCLM L.toContinuousLinearEquiv h ∘ toDistribution :=
      funext (toDistribution_transportₗ L h h')
    rw [hcomp]
    exact (Distribution.transportCLM L.toContinuousLinearEquiv h).continuous.comp
      continuous_toDistribution⟩

@[simp]
theorem toDistribution_transportCLM (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω') (u : WaveFrontSpace Ω Γ) :
    (transportCLM L h h' u).toDistribution =
      Distribution.transportCLM L.toContinuousLinearEquiv h u.toDistribution :=
  toDistribution_transportₗ L h h' u

/-- The seminorm `‖L^* T‖_{φ,V,N}` is the seminorm `‖T‖_{φ ∘ L⁻¹, L V, N}`. -/
@[simp]
theorem seminorm_transportCLM (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω')
    (i : WaveFrontSeminormIndex Ω' (Prod.map L L ⁻¹' Γ)) (u : WaveFrontSpace Ω Γ) :
    WaveFrontSpace.seminorm i (transportCLM L h h' u) =
      WaveFrontSpace.seminorm (i.transport L h) u :=
  seminorm_transportₗ L h h' i u

end WaveFrontSpace

end TauCeti
