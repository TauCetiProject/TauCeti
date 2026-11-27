/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Basic
public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology.LatticeSeries
public import TauCeti.Analysis.Distribution.WaveFrontSet.Submersion
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Continuity of the pullback along a surjective linear map in the normal topology

Let `A : E →L[ℝ] E'` be a surjective linear map of finite-dimensional real inner product spaces,
mapping an open set `Ω` of `E` into an open set `Ω'` of `E'`. Every complex distribution `T` on
`Ω'` pulls back along `A` by integration over the fibres (`Distribution.compCLMOfSubmersion`),
and the wave front set pulls back with the transpose `Aᵀ`
(`Distribution.waveFrontSet_compCLMOfSubmersion_linear_subset`): if the wave front set of `T` lies
in a cone `Γ`, that of `A^* T` lies in

`Aᵀ Γ = {(x, Aᵀ η) | (A x, η) ∈ Γ}` (`TauCeti.pullbackLinearCone`).

This file proves that the pullback is continuous for the normal topologies of Hörmander's spaces
(`TauCeti.WaveFrontSpace.pullbackLinearCLM`):

`A^* : 𝓓'_Γ(Ω') →L[ℂ] 𝓓'_{Aᵀ Γ}(Ω)`,

for every cone `Γ` of nonzero covectors over `Ω'`, closed in `Ω' × (E' \ {0})`. Since `Aᵀ` is
injective, no conormal condition on `Γ` is needed, unlike for the restriction
`TauCeti.WaveFrontSpace.pullbackInlCLM` (Brouder, Dang and Hélein, Theorem 6.3, for a linear
submersion). Projections of products are the typical example: along `(x, y) ↦ y` the pullback is
`T ↦ 1 ⊗ T`.

## The estimates

The localized Fourier transform of `A^* T` with a cutoff `φ` is the lattice series

`A^* T (φ e_ξ) = ∑ m, (covolume L)⁻¹ 𝓕 φ (ξ + Aᵀ m) T (χ e_(-m))`

(`Distribution.localFourier_compCLMOfSubmersion_linear_eq_tsum`), for a cutoff `χ` equal to one on
`A '' supp φ` and a lattice `L` of `E'` none of whose nonzero vectors translates `supp χ` into a set
meeting it. This is the Fourier series of the fibre integral `A_♯ (φ e_ξ)` in the modulations of
`χ`: by the defining identity of fibre integration, its Fourier coefficients are
`𝓕 φ (ξ + Aᵀ m)`. For a seminorm `‖A^* T‖_{φ,V,N}` of the target, the cutoff `χ` is chosen so that
no point of `Γ` lies over its support in a direction `η` with `dist (Aᵀ η, V) ≤ ε ‖η‖`
(`TauCeti.WaveFrontSpace.exists_cutoff_eqOn_one_forall_notMem`), and the lattice series is bounded
by a continuous seminorm of `𝓓'_Γ(Ω')`
(`TauCeti.WaveFrontSpace.exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le`). For the
topology of `𝓓'(Ω)`, the same holds at `ξ = 0` for the cutoffs in a compact set
(`TauCeti.WaveFrontSpace.exists_continuous_seminorm_norm_tsum_le`).

## Main declarations

* `TauCeti.WaveFrontSpace.pullbackLinearCLM`: the pullback `A^* : 𝓓'_Γ(Ω') →L[ℂ] 𝓓'_{Aᵀ Γ}(Ω)`.
* `TauCeti.WaveFrontSpace.toDistribution_pullbackLinearCLM`: it is
  `Distribution.compCLMOfSubmersion`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the pullback and its sequential continuity on `𝓓'_Γ`).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, Theorem 6.3 (continuity of the pullback in the normal topology).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform ContDiff RealInnerProductSpace InnerProduct

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

namespace TauCeti

namespace WaveFrontSpace

open Distribution ContinuousLinearMap

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  {A : E →L[ℝ] E'} {Ω : Opens E} {Ω' : Opens E'} {Γ : Set (E' × E')}

/-- **The seminorms of the pullback.** For the data `(φ, V, N)` of a seminorm of
`𝓓'_{Aᵀ Γ}(Ω)`, the decay estimate `(1 + ‖ξ‖) ^ N ‖A^* T (φ e_ξ)‖ ≤ p T` on `V` holds for a
continuous seminorm `p` of `𝓓'_Γ(Ω')`. -/
private theorem exists_seminorm_localFourier_le (hAΩ : MapsTo A Ω Ω')
    (hA : Function.Surjective A) (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (j : WaveFrontSeminormIndex Ω (pullbackLinearCone A Γ)) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω' Γ), Continuous p ∧ ∀ u : WaveFrontSpace Ω' Γ,
      ∀ ξ ∈ j.cone, (1 + ‖ξ‖) ^ j.order * ‖(compCLMOfSubmersion volume volume A
        A.contDiff.contDiffOn hAΩ (fun x _ ↦ surjective_fderiv_of_surjective hA x)
          u.toDistribution).localFourier j.cutoff ξ‖ ≤ p u := by
  rcases j.cone.eq_empty_or_nonempty with hV | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, continuous_const, fun u ξ hξ ↦ by simp [hV] at hξ⟩
  have hV0 := j.isClosed_cone.zero_mem_of_smul_mem j.smul_mem_cone hξ₀
  -- No covector of `Γ` over `A '' supp φ` is sent by `Aᵀ` into `V`.
  have hKV : ∀ y ∈ A '' tsupport j.cutoff, ∀ η, (y, η) ∈ Γ → (A†) η ∉ j.cone := by
    rintro _ ⟨x, hx, rfl⟩ η hη hηV
    exact disjoint_left.1 j.disjoint (mk_mem_prod hx hηV) (mem_pullbackLinearCone.2 ⟨η, hη, rfl⟩)
  obtain ⟨ε, hε, χ, hχ1, hχΓ⟩ := exists_cutoff_eqOn_one_forall_notMem (A†) hΓ hcone hΓ0
    (j.cutoff.hasCompactSupport.isCompact.image A.continuous)
    (image_subset_iff.2 fun x hx ↦ hAΩ (j.cutoff.tsupport_subset hx)) j.isClosed_cone hV0
    j.smul_mem_cone hKV
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  obtain ⟨p, hp, hpV⟩ := exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le (A†)
    j.isClosed_cone j.smul_mem_cone hε hχΓ L j.cutoff j.order
  refine ⟨p, hp, fun u ξ hξ ↦ ?_⟩
  rw [localFourier_compCLMOfSubmersion_linear_eq_tsum hAΩ _ hχ1 L hL ξ]
  exact hpV u ξ hξ

/-- **The pullback on a compact set of test functions.** For a compact set `Q` of complex test
functions supported in a common compact subset `K` of `Ω`, the values `A^* T φ`, `φ ∈ Q`, are
bounded by a continuous seminorm of `𝓓'_Γ(Ω')`. -/
private theorem exists_seminorm_localFourier_zero_le (hAΩ : MapsTo A Ω Ω')
    (hA : Function.Surjective A) (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) {Q : Set 𝓓(Ω, ℂ)} (hQ : IsCompact Q)
    (hQK : ∀ φ ∈ Q, tsupport φ ⊆ K) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω' Γ), Continuous p ∧ ∀ u : WaveFrontSpace Ω' Γ, ∀ φ ∈ Q,
      ‖(compCLMOfSubmersion volume volume A A.contDiff.contDiffOn hAΩ
        (fun x _ ↦ surjective_fderiv_of_surjective hA x) u.toDistribution).localFourier φ 0‖ ≤
          p u := by
  -- Since `Aᵀ` is injective, no covector of `Γ` is sent to `0`.
  have hinj : Function.Injective (A†) :=
    ContinuousLinearMap.adjoint_injective_iff_denseRange.2 hA.denseRange
  obtain ⟨ε, hε, χ, hχ1, hχΓ⟩ := exists_cutoff_eqOn_one_forall_notMem (A†) hΓ hcone hΓ0
    (K.isCompact.image A.continuous) (image_subset_iff.2 fun x hx ↦ hAΩ (hKΩ hx))
    isClosed_singleton (mem_singleton 0) forall_smul_mem_singleton_zero fun y _ η hη h0 ↦
      hΓ0 _ hη ((map_eq_zero_iff _ hinj).1 (mem_singleton_iff.1 h0))
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  obtain ⟨p, hp, hpQ⟩ := exists_continuous_seminorm_norm_tsum_le (A†) hε
    (fun p hp η hη ↦ hχΓ p hp η (by simpa using hη)) L hQ
  refine ⟨p, hp, fun u φ hφ ↦ ?_⟩
  rw [localFourier_compCLMOfSubmersion_linear_eq_tsum hAΩ _
    (hχ1.mono (image_mono (hQK φ hφ))) L hL 0]
  simp only [zero_add]
  exact hpQ u φ hφ

/-- The pullback `A^* : 𝓓'_Γ(Ω') → 𝓓'_{Aᵀ Γ}(Ω)` as a linear map, before its continuity is
proved. -/
private def pullbackLinearₗ (hAΩ : MapsTo A Ω Ω') (hA : Function.Surjective A) :
    WaveFrontSpace Ω' Γ →ₗ[ℂ] WaveFrontSpace Ω (pullbackLinearCone A Γ) where
  toFun u := mk (compCLMOfSubmersion volume volume A A.contDiff.contDiffOn hAΩ
      (fun x _ ↦ surjective_fderiv_of_surjective hA x) u.toDistribution)
    (waveFrontSet_compCLMOfSubmersion_linear_subset volume volume hAΩ
      u.waveFrontSet_toDistribution_subset)
  map_add' u v := ext <| by simp only [toDistribution_mk, map_add]
  map_smul' c u := ext <| by
    simp only [toDistribution_mk, map_smul, RingHom.id_apply]
    ext φ
    simp [compCLMOfSubmersion_apply]

private theorem toDistribution_pullbackLinearₗ (hAΩ : MapsTo A Ω Ω')
    (hA : Function.Surjective A) (u : WaveFrontSpace Ω' Γ) :
    (pullbackLinearₗ hAΩ hA u).toDistribution = compCLMOfSubmersion volume volume A
      A.contDiff.contDiffOn hAΩ (fun x _ ↦ surjective_fderiv_of_surjective hA x)
        u.toDistribution :=
  toDistribution_mk _ _

/-- **Continuity of the pullback along a surjective linear map in the normal topology.** Let
`A : E →L[ℝ] E'` be surjective, mapping `Ω` into `Ω'`, and let `Γ` be a cone of nonzero
covectors over `Ω'`, closed in `Ω' × (E' \ {0})`. Then the pullback `A^* T` by integration over
the fibres of `A` (`Distribution.compCLMOfSubmersion`) is a continuous linear map from
`𝓓'_Γ(Ω')` to `𝓓'_{Aᵀ Γ}(Ω)`, where `Aᵀ Γ = {(x, Aᵀ η) | (A x, η) ∈ Γ}` (Brouder, Dang and
Hélein, Theorem 6.3, for a linear submersion). -/
def pullbackLinearCLM (A : E →L[ℝ] E') (hAΩ : MapsTo A Ω Ω') (hA : Function.Surjective A)
    (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0) :
    WaveFrontSpace Ω' Γ →L[ℂ] WaveFrontSpace Ω (pullbackLinearCone A Γ) :=
  ⟨pullbackLinearₗ hAΩ hA, continuous_linearMap_of_forall_isCompact_le _
    (fun _ hKΩ _ hQ hQK ↦ by
      simpa only [toDistribution_pullbackLinearₗ] using
        exists_seminorm_localFourier_zero_le hAΩ hA hΓ hcone hΓ0 hKΩ hQ hQK)
    fun j ↦ by
      simpa only [toDistribution_pullbackLinearₗ] using
        exists_seminorm_localFourier_le hAΩ hA hΓ hcone hΓ0 j⟩

@[simp]
theorem toDistribution_pullbackLinearCLM (hAΩ : MapsTo A Ω Ω') (hA : Function.Surjective A)
    (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (u : WaveFrontSpace Ω' Γ) :
    (pullbackLinearCLM A hAΩ hA hΓ hcone hΓ0 u).toDistribution =
      compCLMOfSubmersion volume volume A A.contDiff.contDiffOn hAΩ
        (fun x _ ↦ surjective_fderiv_of_surjective hA x) u.toDistribution :=
  toDistribution_pullbackLinearₗ hAΩ hA u

end WaveFrontSpace

end TauCeti
