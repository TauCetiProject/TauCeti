/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic

/-!
# Wave front sets under transport along linear isometries

Let `L : E' ≃ₗᵢ[ℝ] E` be a linear isometry between real inner product spaces, possibly different
and of any dimension, identifying an open set `Ω'` of `E'` with an open set `Ω` of `E`. A
distribution `T` on `Ω` transports to the distribution `L^* T = φ ↦ T (φ ∘ L⁻¹)` on `Ω'`
(`Distribution.transportCLM`). Since `L` preserves inner products, the Fourier atom
`x ↦ 𝐞 (-⟪x, η⟫)` on `E'` is the transport of the Fourier atom of `L η` on `E`, so the localized
Fourier transforms of `L^* T` are those of `T`, with transported cutoffs, at the frequencies `L η`
(`Distribution.localFourier_transportCLM`). Hence positions and frequencies of the wave front set
both move by `L`:

`WF(L^* T) = {(x, ξ) | (L x, L ξ) ∈ WF(T)}`

(`Distribution.waveFrontSet_transportCLM`). This is the case of
`Distribution.waveFrontSet_compCLMOfContinuousLinearEquiv` between two different spaces, for an
isometry: then the transpose inverse of `L` is `L` itself and no Jacobian factor appears. Every
linear isomorphism between two finite-dimensional inner product spaces is such an isometry
followed by a linear automorphism, which that lemma covers. A typical use is the swap
`WithLp 2 (E × D) ≃ₗᵢ[ℝ] WithLp 2 (D × E)` of the factors of a Euclidean product.

## Main declarations

* `Distribution.localFourier_transportCLM`: the localized Fourier transform of `L^* T`.
* `Distribution.isMicrolocallySmoothAt_transportCLM_iff`: `L^* T` is microlocally smooth at
  `(x, ξ)` exactly when `T` is at `(L x, L ξ)`.
* `Distribution.waveFrontSet_transportCLM`: the wave front set of `L^* T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2, Theorem 8.2.4 (the wave front set under a change of coordinates).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction
open scoped Distributions RealInnerProductSpace

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'}

/-- **Localized Fourier transforms under transport along a linear isometry.** The localized
Fourier transform of the transport `L^* T` with cutoff `φ`, at the frequency `η`, is that of `T`
with the transported cutoff `φ ∘ L⁻¹`, at the frequency `L η`. -/
theorem localFourier_transportCLM (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω', ℂ)) (η : E') :
    (transportCLM L.toContinuousLinearEquiv h T).localFourier φ η =
      T.localFourier (L.toContinuousLinearEquiv.transportTestFunction ℝ h φ) (L η) := by
  rw [localFourier_def, complexPairing_transportCLM]
  refine (localFourier_eq _ _ fun y ↦ ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    LinearIsometryEquiv.inner_map_eq_flip]

/-- If `T` is microlocally smooth at `(L x, L ξ)`, then its transport along the linear isometry
`L` is microlocally smooth at `(x, ξ)`. Here `L` identifies `Ω'` with `Ω`. -/
theorem IsMicrolocallySmoothAt.transportCLM {T : 𝓓'(Ω, ℂ)} {x ξ : E'} (L : E' ≃ₗᵢ[ℝ] E)
    (h : MapsTo L.toContinuousLinearEquiv Ω' Ω) (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω')
    (hT : T.IsMicrolocallySmoothAt (L x) (L ξ)) :
    (transportCLM L.toContinuousLinearEquiv h T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hT
  -- The cutoff `φ ∘ L` and the cone `L⁻¹ Γ` carry the decay of `T` over to its transport.
  refine isMicrolocallySmoothAt_iff.2
    ⟨L.toContinuousLinearEquiv.symm.transportTestFunction ℝ h' φ, by simpa using hφ,
    L ⁻¹' Γ, hΓ.preimage L.continuous, hξ, fun t ht η hη ↦ ?_, fun N ↦ ?_⟩
  · simpa only [mem_preimage, map_smul] using hcone t ht (L η) hη
  obtain ⟨C, hC⟩ := hdecay N
  refine ⟨C, fun η hη ↦ ?_⟩
  rw [localFourier_transportCLM,
    ContinuousLinearEquiv.transportTestFunction_transportTestFunction_symm, ← L.norm_map η]
  exact hC (L η) hη

/-- **Microlocal smoothness under transport along a linear isometry.** When the linear isometry
`L` identifies `Ω'` with `Ω`, the transport `L^* T` is microlocally smooth at `(x, ξ)` exactly
when `T` is microlocally smooth at `(L x, L ξ)`. -/
theorem isMicrolocallySmoothAt_transportCLM_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E'} (L : E' ≃ₗᵢ[ℝ] E)
    (h : MapsTo L.toContinuousLinearEquiv Ω' Ω) (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω') :
    (transportCLM L.toContinuousLinearEquiv h T).IsMicrolocallySmoothAt x ξ ↔
      T.IsMicrolocallySmoothAt (L x) (L ξ) := by
  refine ⟨fun hT ↦ ?_, fun hT ↦ hT.transportCLM L h h'⟩
  -- Transport `L^* T` back along `L⁻¹`, which gives back `T`.
  have hT' : (transportCLM L.toContinuousLinearEquiv h T).IsMicrolocallySmoothAt
      (L.symm (L x)) (L.symm (L ξ)) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hT
  have hT'' : (transportCLM L.toContinuousLinearEquiv.symm h'
      (transportCLM L.toContinuousLinearEquiv h T)).IsMicrolocallySmoothAt (L x) (L ξ) :=
    hT'.transportCLM L.symm h' h
  rwa [transportCLM_symm_transportCLM] at hT''

/-- **The wave front set under transport along a linear isometry.** When the linear isometry `L`
identifies `Ω'` with `Ω`, the wave front set of the transport `L^* T` consists of the `(x, ξ)`
with `(L x, L ξ)` in the wave front set of `T`: positions and covectors both move by `L⁻¹`. -/
theorem waveFrontSet_transportCLM (L : E' ≃ₗᵢ[ℝ] E) (h : MapsTo L.toContinuousLinearEquiv Ω' Ω)
    (h' : MapsTo L.toContinuousLinearEquiv.symm Ω Ω') (T : 𝓓'(Ω, ℂ)) :
    (transportCLM L.toContinuousLinearEquiv h T).waveFrontSet =
      Prod.map L L ⁻¹' T.waveFrontSet := by
  ext ⟨x, ξ⟩
  have hx : x ∈ Ω' ↔ L x ∈ Ω := ⟨fun hx ↦ h hx, fun hx ↦ by simpa using h' hx⟩
  simp only [mem_waveFrontSet_iff, mem_preimage, Prod.map_apply, hx, ne_eq,
    LinearIsometryEquiv.map_eq_zero_iff, isMicrolocallySmoothAt_transportCLM_iff L h h']

end Distribution
