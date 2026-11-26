/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology.LatticeSeries
public import TauCeti.Analysis.Distribution.WaveFrontSet.Submersion
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Analysis.Distribution.TestFunction.Compact
import TauCeti.Analysis.Distribution.TestFunction.FourierAtom
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Continuity of the pullback along a surjective linear map in the normal topology

Let `A : E →L[ℝ] E'` be a surjective linear map of finite-dimensional real inner product spaces,
mapping an open set `Ω` of `E` into an open set `Ω'` of `E'`. Every complex distribution `T` on
`Ω'` pulls back along `A` by integration over the fibres (`Distribution.compCLMOfSubmersion`),
and the wave front set pulls back with the transpose `Aᵀ`
(`Distribution.waveFrontSet_compCLMOfSubmersion`): if the wave front set of `T` lies in a cone
`Γ`, that of `A^* T` lies in

`Aᵀ Γ = {(x, Aᵀ η) | (A x, η) ∈ Γ}` (`TauCeti.pullbackLinearCone`).

This file proves that the pullback is continuous for the normal topologies of Hörmander's spaces
(`TauCeti.WaveFrontSpace.pullbackLinearCLM`):

`A^* : 𝓓'_Γ(Ω') →L[ℂ] 𝓓'_{Aᵀ Γ}(Ω)`,

for every cone `Γ` of nonzero covectors over `Ω'`, closed in `Ω' × (E' \ {0})`. Since `Aᵀ` is
injective, no condition on `Γ` is needed (Brouder, Dang and Hélein, Theorem 6.3, for a linear
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

* `TauCeti.pullbackLinearCone`: the cone `Aᵀ Γ`.
* `Distribution.localFourier_compCLMOfSubmersion_linear_eq_tsum`: the lattice series of the
  localized Fourier transform of `A^* T`.
* `Distribution.waveFrontSet_compCLMOfSubmersion_linear_subset`: `WF(T) ⊆ Γ` implies
  `WF(A^* T) ⊆ Aᵀ Γ`.
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

/-- The pullback `Aᵀ Γ = {(x, Aᵀ η) | (A x, η) ∈ Γ}` of a set `Γ` of covectors on `E'` along a
linear map `A : E →L[ℝ] E'`. It contains the wave front set of the pullback along `A` of a
distribution with wave front set in `Γ`
(`Distribution.waveFrontSet_compCLMOfSubmersion_linear_subset`). -/
def pullbackLinearCone (A : E →L[ℝ] E') (Γ : Set (E' × E')) : Set (E × E) :=
  {p | ∃ η, (A p.1, η) ∈ Γ ∧ (A†) η = p.2}

@[simp]
theorem mem_pullbackLinearCone {A : E →L[ℝ] E'} {Γ : Set (E' × E')} {p : E × E} :
    p ∈ pullbackLinearCone A Γ ↔ ∃ η, (A p.1, η) ∈ Γ ∧ (A†) η = p.2 :=
  Iff.rfl

theorem pullbackLinearCone_mono {A : E →L[ℝ] E'} {Γ Γ' : Set (E' × E')} (h : Γ ⊆ Γ') :
    pullbackLinearCone A Γ ⊆ pullbackLinearCone A Γ' :=
  fun _ ⟨η, hη, hη'⟩ ↦ ⟨η, h hη, hη'⟩

end TauCeti

namespace Distribution

open TauCeti

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  {A : E →L[ℝ] E'} {Ω : Opens E} {Ω' : Opens E'} {hf : ContDiffOn ℝ ∞ A Ω}
  {hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ A x)}

/-- **The localized Fourier transform of a pullback along a linear map as a lattice series.** Let
`χ` be equal to one on the image under `A` of the support of `φ`, and let the translates of
`tsupport χ` by the lattice `L` meet it only for the translation `0`. Then

`A^* T (φ e_ξ) = ∑ m ∈ L*, (covolume L)⁻¹ 𝓕 φ (ξ + Aᵀ m) T (χ e_(-m))`. -/
theorem localFourier_compCLMOfSubmersion_linear_eq_tsum (hAΩ : MapsTo A Ω Ω') (T : 𝓓'(Ω', ℂ))
    {φ : 𝓓(Ω, ℂ)} {χ : 𝓓(Ω', ℂ)} (hχ : EqOn χ 1 (A '' tsupport φ)) (L : Submodule ℤ E')
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ y ∈ tsupport χ, ∀ ℓ ∈ L, y + ℓ ∈ tsupport χ → ℓ = 0) (ξ : E) :
    (compCLMOfSubmersion volume volume A hf hAΩ hsurj T).localFourier φ ξ =
      ∑' m : ZLattice.dual L, (ZLattice.covolume L : ℂ)⁻¹ *
        (𝓕 (φ : E → ℂ) (ξ + (A†) m) * T.localFourier χ (-m)) := by
  -- The fibre integral `g` of `ψ = φ e_ξ`, a complex test function on `Ω'`.
  set ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ξ) φ
  have hψφ : tsupport ψ ⊆ tsupport φ := fun x hx ↦ by
    simp only [ψ, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply'] at hx
    exact tsupport_mul_subset_left hx
  obtain ⟨g, hgK, hg⟩ := exists_integral_mul_eq_integral_mul_comp volume volume hf hAΩ hsurj ψ
  have h1 : (compCLMOfSubmersion volume volume A hf hAΩ hsurj T).localFourier φ ξ =
      T.complexPairing g := by
    rw [localFourier_def]
    exact complexPairing_compCLMOfSubmersion volume volume hf hAΩ hsurj T fun h hh _ _ ↦
      hg _ (continuous_ofReal.comp hh.continuous).continuousOn
  -- The Fourier coefficients of `g` are `𝓕 φ (ξ + Aᵀ m)`.
  have hcoeff (m : E') : 𝓕 (g : E' → ℂ) m = 𝓕 (φ : E → ℂ) (ξ + (A†) m) := by
    have hcont : Continuous fun y : E' ↦ (𝐞 (-⟪y, m⟫) : ℂ) := by fun_prop
    rw [add_comm, ← TestFunction.fourier_bilinLeftCLM_fourierAtom φ ξ, Real.fourier_eq,
      Real.fourier_eq]
    simp only [Circle.smul_def]
    calc ∫ y, (𝐞 (-⟪y, m⟫) : ℂ) * g y = ∫ y, g y * (𝐞 (-⟪y, m⟫) : ℂ) :=
          integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
      _ = ∫ x, ψ x * (𝐞 (-⟪A x, m⟫) : ℂ) := hg _ hcont.continuousOn
      _ = ∫ x, (𝐞 (-⟪x, (A†) m⟫) : ℂ) * ψ x :=
          integral_congr_ae (Eventually.of_forall fun x ↦ by
            dsimp only
            rw [ContinuousLinearMap.adjoint_inner_right, mul_comm])
  have hsupp : EqOn (χ : E' → ℂ) 1 (support g) :=
    fun y hy ↦ hχ (image_mono hψφ (hgK (subset_tsupport _ hy)))
  rw [h1, ← (hasSum_fourier_mul_localFourier T χ L hL hsupp).tsum_eq]
  congr 1 with m
  rw [hcoeff, mul_assoc]

/-- **The wave front set of a pullback along a linear map.** If the wave front set of `T` lies in
`Γ`, that of its pullback along `A` lies in `Aᵀ Γ = {(x, Aᵀ η) | (A x, η) ∈ Γ}`. -/
theorem waveFrontSet_compCLMOfSubmersion_linear_subset (hAΩ : MapsTo A Ω Ω') {T : 𝓓'(Ω', ℂ)}
    {Γ : Set (E' × E')} (hT : T.waveFrontSet ⊆ Γ) :
    (compCLMOfSubmersion volume volume A hf hAΩ hsurj T).waveFrontSet ⊆
      pullbackLinearCone A Γ := by
  rw [waveFrontSet_compCLMOfSubmersion]
  rintro ⟨x, ξ⟩ ⟨-, η, hη, hξ⟩
  exact ⟨η, hT hη, by simpa only [A.fderiv] using hξ⟩

end Distribution

namespace TauCeti

namespace WaveFrontSpace

open Distribution

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  {A : E →L[ℝ] E'} {Ω : Opens E} {Ω' : Opens E'} {Γ : Set (E' × E')}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] in
/-- A surjective linear map is a submersion. -/
private theorem surjective_fderiv (hA : Function.Surjective A) :
    ∀ x ∈ Ω, Function.Surjective (fderiv ℝ A x) :=
  fun _ _ ↦ by rwa [A.fderiv]

/-- **The seminorms of the pullback.** For the data `(φ, V, N)` of a seminorm of
`𝓓'_{Aᵀ Γ}(Ω)`, the decay estimate `(1 + ‖ξ‖) ^ N ‖A^* T (φ e_ξ)‖ ≤ p T` on `V` holds for a
continuous seminorm `p` of `𝓓'_Γ(Ω')`. -/
private theorem exists_seminorm_localFourier_le (hAΩ : MapsTo A Ω Ω')
    (hA : Function.Surjective A) (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (j : WaveFrontSeminormIndex Ω (pullbackLinearCone A Γ)) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω' Γ), Continuous p ∧ ∀ u : WaveFrontSpace Ω' Γ,
      ∀ ξ ∈ j.cone, (1 + ‖ξ‖) ^ j.order * ‖(compCLMOfSubmersion volume volume A
        A.contDiff.contDiffOn hAΩ (surjective_fderiv hA) u.toDistribution).localFourier
          j.cutoff ξ‖ ≤ p u := by
  rcases j.cone.eq_empty_or_nonempty with hV | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, continuous_const, fun u ξ hξ ↦ by simp [hV] at hξ⟩
  have hV0 := j.isClosed_cone.zero_mem_of_smul_mem j.smul_mem_cone hξ₀
  -- No covector of `Γ` over `A '' supp φ` is sent by `Aᵀ` into `V`.
  have hKV : ∀ y ∈ A '' tsupport j.cutoff, ∀ η, (y, η) ∈ Γ → (A†) η ∉ j.cone := by
    rintro _ ⟨x, hx, rfl⟩ η hη hηV
    exact disjoint_left.1 j.disjoint (mk_mem_prod hx hηV) ⟨η, hη, rfl⟩
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

/-- **The pullback on a compact set of test functions.** For a compact set `Q` of real test
functions on `Ω`, the values `A^* T ψ`, `ψ ∈ Q`, are bounded by a continuous seminorm of
`𝓓'_Γ(Ω')`. -/
private theorem exists_seminorm_apply_le (hAΩ : MapsTo A Ω Ω') (hA : Function.Surjective A)
    (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {Q : Set 𝓓(Ω, ℝ)} (hQ : IsCompact Q) :
    ∃ p : Seminorm ℂ (WaveFrontSpace Ω' Γ), Continuous p ∧ ∀ u : WaveFrontSpace Ω' Γ, ∀ ψ ∈ Q,
      ‖compCLMOfSubmersion volume volume A A.contDiff.contDiffOn hAΩ (surjective_fderiv hA)
        u.toDistribution ψ‖ ≤ p u := by
  -- The complexified test functions of `Q` are supported in one compact set `K`.
  set Qc : Set 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM '' Q
  have hQc : IsCompact Qc := hQ.image (postcompCLM _).continuous
  obtain ⟨K, hKΩ, hQK⟩ := TestFunction.exists_compacts_forall_tsupport_subset_of_isCompact hQc
  have hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ ({0} : Set E), t • ξ ∈ ({0} : Set E) := by
    rintro t - ξ rfl
    simp
  -- Since `Aᵀ` is injective, no covector of `Γ` is sent to `0`.
  have hinj : Function.Injective (A†) :=
    ContinuousLinearMap.adjoint_injective_iff_denseRange.2 hA.denseRange
  obtain ⟨ε, hε, χ, hχ1, hχΓ⟩ := exists_cutoff_eqOn_one_forall_notMem (A†) hΓ hcone hΓ0
    (K.isCompact.image A.continuous) (image_subset_iff.2 fun x hx ↦ hAΩ (hKΩ hx))
    isClosed_singleton (mem_singleton 0) hVcone fun y _ η hη h0 ↦
      hΓ0 _ hη ((map_eq_zero_iff _ hinj).1 (mem_singleton_iff.1 h0))
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  obtain ⟨p, hp, hpQ⟩ := exists_continuous_seminorm_norm_tsum_le (A†) hε
    (fun p hp η hη ↦ hχΓ p hp η (by simpa using hη)) L hQc
  refine ⟨p, hp, fun u ψ hψ ↦ ?_⟩
  -- `A^* T ψ` is the localized Fourier transform of `A^* T` with cutoff `ψ` at `0`.
  set ψc := postcompCLM (𝕜 := ℝ) ofRealCLM ψ
  set S := compCLMOfSubmersion volume volume A A.contDiff.contDiffOn hAΩ (surjective_fderiv hA)
    u.toDistribution
  have hψc : S ψ = S.localFourier ψc 0 := by
    rw [localFourier_at_zero, complexPairing_postcompCLM_ofRealCLM]
  rw [hψc, localFourier_compCLMOfSubmersion_linear_eq_tsum hAΩ _
    (hχ1.mono (image_mono (hQK _ ⟨ψ, hψ, rfl⟩))) L hL 0]
  simp only [zero_add]
  exact hpQ u ψc ⟨ψ, hψ, rfl⟩

/-- The pullback `A^* : 𝓓'_Γ(Ω') → 𝓓'_{Aᵀ Γ}(Ω)` as a linear map, before its continuity is
proved. -/
private def pullbackLinearₗ (hAΩ : MapsTo A Ω Ω') (hA : Function.Surjective A) :
    WaveFrontSpace Ω' Γ →ₗ[ℂ] WaveFrontSpace Ω (pullbackLinearCone A Γ) where
  toFun u := mk (compCLMOfSubmersion volume volume A A.contDiff.contDiffOn hAΩ
      (surjective_fderiv hA) u.toDistribution)
    (waveFrontSet_compCLMOfSubmersion_linear_subset hAΩ u.waveFrontSet_toDistribution_subset)
  map_add' u v := ext <| by simp only [toDistribution_mk, map_add]
  map_smul' c u := ext <| by
    simp only [toDistribution_mk, map_smul, RingHom.id_apply]
    ext φ
    simp [compCLMOfSubmersion_apply]

private theorem toDistribution_pullbackLinearₗ (hAΩ : MapsTo A Ω Ω')
    (hA : Function.Surjective A) (u : WaveFrontSpace Ω' Γ) :
    (pullbackLinearₗ hAΩ hA u).toDistribution = compCLMOfSubmersion volume volume A
      A.contDiff.contDiffOn hAΩ (surjective_fderiv hA) u.toDistribution :=
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
  ⟨pullbackLinearₗ hAΩ hA, by
    refine continuous_linearMap_of_le _ ?_ fun j ↦ ?_
    · -- Continuity into `𝓓'(Ω)`: the values on a compact set of test functions.
      refine continuous_of_tendsto_nhds_zero (toDistribution ∘ₗ pullbackLinearₗ hAΩ hA) ?_
      refine CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_right_iff.2 fun ⟨Q, V'⟩ ⟨hQ, hV'⟩ ↦ ?_
      obtain ⟨r, hr, hrV'⟩ := Metric.mem_nhds_iff.1 hV'
      obtain ⟨p, hp, hpQ⟩ := exists_seminorm_apply_le hAΩ hA hΓ hcone hΓ0 hQ
      filter_upwards [(hp.tendsto' 0 0 (map_zero p)) (Iio_mem_nhds hr)] with u hu ψ hψ
      have h := hpQ u ψ hψ
      rw [LinearMap.coe_comp, Function.comp_apply, toDistribution_pullbackLinearₗ]
      exact hrV' (mem_ball_zero_iff.2 (h.trans_lt hu))
    · -- The seminorms of the target.
      obtain ⟨p, hp, hpj⟩ := exists_seminorm_localFourier_le hAΩ hA hΓ hcone hΓ0 j
      refine ⟨p, hp, fun u ↦ seminorm_le_bound j _ (apply_nonneg _ _) fun ξ hξ ↦ ?_⟩
      simpa only [toDistribution_pullbackLinearₗ] using hpj u ξ hξ⟩

@[simp]
theorem toDistribution_pullbackLinearCLM (hAΩ : MapsTo A Ω Ω') (hA : Function.Surjective A)
    (hΓ : IsOpen (((Ω' : Set E') ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {hf : ContDiffOn ℝ ∞ A Ω} {hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ A x)}
    (u : WaveFrontSpace Ω' Γ) :
    (pullbackLinearCLM A hAΩ hA hΓ hcone hΓ0 u).toDistribution =
      compCLMOfSubmersion volume volume A hf hAΩ hsurj u.toDistribution :=
  toDistribution_pullbackLinearₗ hAΩ hA u

end WaveFrontSpace

end TauCeti
