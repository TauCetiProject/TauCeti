/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LinearEquiv
public import TauCeti.Analysis.Distribution.Restriction
public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.Distribution.TestFunction.ChangeOfVariables
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Distributions under smooth changes of variables

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real normed space `E` whose
inverse is smooth as well, so `e` is a diffeomorphism from its source onto its target. Let `U` be an
open subset of the source and `Ω` an open set containing `e '' U`. A distribution `T` on `Ω` pulls
back along `e` to the distribution on `U`

`(e^* T) φ = T (e_* φ)`, where `(e_* φ) y = |det D e⁻¹ (y)| φ (e⁻¹ y)`

is the pushforward of the test density `φ` (`TestFunction.pushforwardCLM`). This is the formula
that makes pullback agree with composition on functions: on a locally integrable function `f`,
`e^* f = f ∘ e` (`Distribution.compCLMOfOpenPartialHomeomorph_ofFun`). The point mass at `e x`
pulls back to `|det D e (x)|⁻¹` times the point mass at `x`. Pulling back along a composite is the
composite of the pullbacks, and pulling back along `e` and then along `e⁻¹` gives back the original
distribution, in both orders; pullback commutes with restriction to
smaller open sets and, for complex distributions, with the complex-linear extension to complex
test functions. For a continuous linear automorphism it is
`Distribution.compCLMOfContinuousLinearEquiv`.

Pullback along changes of variables is how operations on distributions are transported between
coordinate charts: chart transitions of a manifold are such maps. Near a point, `e` agrees with a
global bijection `Φ` of `E`, and there `e^* T` is the pullback `Φ^* (χ T)` of the tempered
distribution `χ T` for a cutoff `χ` equal to `1` near the image
(`Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`), which reduces local
regularity of pullbacks to global estimates for `TemperedDistribution.compCLM`.

## Main declarations

* `Distribution.compCLMOfOpenPartialHomeomorph`: the pullback `T ↦ e^* T`, as a continuous linear
  map `𝓓'(Ω, F) →L[ℝ] 𝓓'(U, F)`.
* `Distribution.compCLMOfOpenPartialHomeomorph_ofFun`: `e^*` sends the distribution of a locally
  integrable function `f` to that of `f ∘ e`, for any additive Haar measure.
* `Distribution.compCLMOfOpenPartialHomeomorph_delta`: `e^* δ_{e x} = |det D e (x)|⁻¹ δ_x`.
* `Distribution.compCLMOfOpenPartialHomeomorph_refl`: pulling back along the identity is
  restriction.
* `Distribution.dsupport_compCLMOfOpenPartialHomeomorph_inter_source_subset`: on the source of
  `e`, the support of `e^* T` lies in the preimage of the support of `T`.
* `Distribution.compCLMOfOpenPartialHomeomorph_trans`: pulling back along a composite is the
  composite of the pullbacks.
* `Distribution.compCLMOfOpenPartialHomeomorph_symm_apply_apply`,
  `Distribution.compCLMOfOpenPartialHomeomorph_apply_symm_apply`: pulling back along `e` and `e⁻¹`
  are inverse to each other.
* `Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph`: pullback commutes with restriction.
* `Distribution.complexPairing_compCLMOfOpenPartialHomeomorph`: the complex-linear extension of
  `e^* T` to complex test functions is computed by the same formula.
* `Distribution.compCLMOfOpenPartialHomeomorph_eq_compCLMOfContinuousLinearEquiv`: along a
  continuous linear automorphism, the pullback is `Distribution.compCLMOfContinuousLinearEquiv`.
* `Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`: near a point, the
  pullback of a complex distribution is a tempered pullback of a cut-off.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1, (6.1.1)–(6.1.2)
  (pullback of distributions by diffeomorphisms).
-/

public section

noncomputable section

open Filter Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {e : OpenPartialHomeomorph E E} {U V Ω : Opens E}

section General

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The **pullback of a distribution along a smooth change of variables** `e`, a smooth open
partial homeomorphism with smooth inverse, from an open subset `U` of its source to an open set `Ω`
containing `e '' U`: a distribution `T` on `Ω` pulls back to the distribution
`φ ↦ T (e_* φ)` on `U`, where `(e_* φ) y = |det D e⁻¹ (y)| φ (e⁻¹ y)` is the pushforward of test
densities `TestFunction.pushforwardCLM`. On the distribution of a locally integrable function `f`
it gives that of `f ∘ e` (`Distribution.compCLMOfOpenPartialHomeomorph_ofFun`). -/
def compCLMOfOpenPartialHomeomorph (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω) : 𝓓'(Ω, F) →L[ℝ] 𝓓'(U, F) :=
  (pushforwardCLM e he he' hU hUΩ).precompCompactConvergenceCLM F

variable {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- The pullback `e^* T` pairs a test function `φ` with `T` through `T (e_* φ)`. -/
@[simp]
theorem compCLMOfOpenPartialHomeomorph_apply (T : 𝓓'(Ω, F)) (φ : 𝓓(U, ℝ)) :
    compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T φ = T (pushforwardCLM e he he' hU hUΩ φ) :=
  (rfl)

/-- Pulling back along the identity is restriction. -/
@[simp]
theorem compCLMOfOpenPartialHomeomorph_refl
    {he : ContDiffOn ℝ (⊤ : ℕ∞) (OpenPartialHomeomorph.refl E)
      (OpenPartialHomeomorph.refl E).source}
    {he' : ContDiffOn ℝ (⊤ : ℕ∞) (OpenPartialHomeomorph.refl E).symm
      (OpenPartialHomeomorph.refl E).target}
    {hU : (U : Set E) ⊆ (OpenPartialHomeomorph.refl E).source}
    {hUΩ : MapsTo (OpenPartialHomeomorph.refl E) U Ω} :
    (compCLMOfOpenPartialHomeomorph (OpenPartialHomeomorph.refl E) he he' hU hUΩ :
      𝓓'(Ω, F) →L[ℝ] 𝓓'(U, F)) = restrictCLM := by
  ext T φ
  rw [compCLMOfOpenPartialHomeomorph_apply, restrictCLM_apply, pushforwardCLM_refl]

/-- On the source of `e`, the support of the pullback `e^* T` lies in the preimage of the support
of `T`. Off the source, the values of `e` carry no information, so the intersection is needed at
boundary points of `U` outside the source. -/
theorem dsupport_compCLMOfOpenPartialHomeomorph_inter_source_subset (T : 𝓓'(Ω, F)) :
    dsupport (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) ∩ e.source ⊆
      e ⁻¹' dsupport T := by
  rintro x ⟨hx, hxs⟩
  by_contra hxT
  obtain ⟨s, hT, hs, hxs'⟩ := (notMem_dsupport_iff _).1 hxT
  -- `T` vanishes on `s`, so `e^* T` vanishes on `e.source ∩ e ⁻¹' s`, since `e_*` maps test
  -- functions supported there to test functions supported in `s`.
  refine (notMem_dsupport_iff (f := compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) x).2
    ⟨e.source ∩ e ⁻¹' s, fun φ hφ ↦ ?_, e.isOpen_inter_preimage hs, hxs, hxs'⟩ hx
  rw [compCLMOfOpenPartialHomeomorph_apply]
  refine hT _ ((tsupport_pushforwardCLM_subset φ).trans ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact (hφ hy).2

/-- **Functoriality**: pulling back along the composite `e₁.trans e₂` is pulling back along `e₂`
and then along `e₁`. -/
theorem compCLMOfOpenPartialHomeomorph_trans {e₁ e₂ : OpenPartialHomeomorph E E}
    {he₁ : ContDiffOn ℝ (⊤ : ℕ∞) e₁ e₁.source} {he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e₁.symm e₁.target}
    {he₂ : ContDiffOn ℝ (⊤ : ℕ∞) e₂ e₂.source} {he₂' : ContDiffOn ℝ (⊤ : ℕ∞) e₂.symm e₂.target}
    {he : ContDiffOn ℝ (⊤ : ℕ∞) (e₁.trans e₂) (e₁.trans e₂).source}
    {he' : ContDiffOn ℝ (⊤ : ℕ∞) (e₁.trans e₂).symm (e₁.trans e₂).target}
    {hU : (U : Set E) ⊆ e₁.source} {hUV : MapsTo e₁ U V} {hV : (V : Set E) ⊆ e₂.source}
    {hVΩ : MapsTo e₂ V Ω} {hU' : (U : Set E) ⊆ (e₁.trans e₂).source}
    {hUΩ : MapsTo (e₁.trans e₂) U Ω} (T : 𝓓'(Ω, F)) :
    compCLMOfOpenPartialHomeomorph (e₁.trans e₂) he he' hU' hUΩ T =
      compCLMOfOpenPartialHomeomorph e₁ he₁ he₁' hU hUV
        (compCLMOfOpenPartialHomeomorph e₂ he₂ he₂' hV hVΩ T) := by
  ext φ
  rw [compCLMOfOpenPartialHomeomorph_apply, compCLMOfOpenPartialHomeomorph_apply,
    compCLMOfOpenPartialHomeomorph_apply,
    pushforwardCLM_trans (he := he) (he' := he') (hU' := hU') (hUΩ := hUΩ)]

/-- Pulling back along `e` and then along `e⁻¹` gives back the original distribution. -/
@[simp]
theorem compCLMOfOpenPartialHomeomorph_symm_apply_apply
    {he₁ : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.symm.source}
    {he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm.symm e.symm.target}
    {hV : (V : Set E) ⊆ e.symm.source} {hVU : MapsTo e.symm V U} {hUV : MapsTo e U V}
    (T : 𝓓'(V, F)) :
    compCLMOfOpenPartialHomeomorph e.symm he₁ he₁' hV hVU
      (compCLMOfOpenPartialHomeomorph e he he' hU hUV T) = T := by
  ext φ
  simp only [compCLMOfOpenPartialHomeomorph_apply, pushforwardCLM_pushforwardCLM_symm]

/-- Pulling back along `e⁻¹` and then along `e` gives back the original distribution. -/
@[simp]
theorem compCLMOfOpenPartialHomeomorph_apply_symm_apply
    {he₁ : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.symm.source}
    {he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm.symm e.symm.target}
    {hV : (V : Set E) ⊆ e.symm.source} {hVU : MapsTo e.symm V U} {hUV : MapsTo e U V}
    (T : 𝓓'(U, F)) :
    compCLMOfOpenPartialHomeomorph e he he' hU hUV
      (compCLMOfOpenPartialHomeomorph e.symm he₁ he₁' hV hVU T) = T := by
  ext φ
  simp only [compCLMOfOpenPartialHomeomorph_apply, pushforwardCLM_symm_pushforwardCLM]

/-- Pullback commutes with restriction: restricting `e^* T` to an open `U' ≤ U` is pulling back
the restriction of `T` to any open `Ω' ≤ Ω` containing `e '' U'`. -/
theorem restrictCLM_compCLMOfOpenPartialHomeomorph {U' Ω' : Opens E} (hU' : U' ≤ U)
    (hΩ' : Ω' ≤ Ω) {hU'' : (U' : Set E) ⊆ e.source} {hUΩ' : MapsTo e U' Ω'} (T : 𝓓'(Ω, F)) :
    (restrictCLM (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) : 𝓓'(U', F)) =
      compCLMOfOpenPartialHomeomorph e he he' hU'' hUΩ' (restrictCLM T) := by
  ext φ
  rw [restrictCLM_apply, compCLMOfOpenPartialHomeomorph_apply,
    compCLMOfOpenPartialHomeomorph_apply, restrictCLM_apply, monoCLM_pushforwardCLM hU' hΩ']

/-- Along a continuous linear automorphism `L`, the pullback is
`Distribution.compCLMOfContinuousLinearEquiv`. -/
theorem compCLMOfOpenPartialHomeomorph_eq_compCLMOfContinuousLinearEquiv (L : E ≃L[ℝ] E)
    {hL : ContDiffOn ℝ (⊤ : ℕ∞) L.toHomeomorph.toOpenPartialHomeomorph
      L.toHomeomorph.toOpenPartialHomeomorph.source}
    {hL' : ContDiffOn ℝ (⊤ : ℕ∞) L.toHomeomorph.toOpenPartialHomeomorph.symm
      L.toHomeomorph.toOpenPartialHomeomorph.target}
    {hU : (U : Set E) ⊆ L.toHomeomorph.toOpenPartialHomeomorph.source} (hUΩ : MapsTo L U Ω) :
    (compCLMOfOpenPartialHomeomorph L.toHomeomorph.toOpenPartialHomeomorph hL hL' hU hUΩ :
      𝓓'(Ω, F) →L[ℝ] 𝓓'(U, F)) = compCLMOfContinuousLinearEquiv L hUΩ := by
  ext T φ
  -- Both sides unfold by their `rfl` application lemmas; `hUΩ` is stated for `L` rather than for
  -- its coercion to a partial homeomorphism, so this is closed by unification, not rewriting.
  exact ((congrArg T (pushforwardCLM_eq_smul_transportTestFunction L hUΩ φ)).trans
    (map_smul T _ _)).trans (compCLMOfContinuousLinearEquiv_apply L hUΩ T φ).symm

end General

/-- The pullback of the point mass at `e x`, for `x` in the source of `e`, is
`|det D e (x)|⁻¹` times the point mass at `x`. -/
theorem compCLMOfOpenPartialHomeomorph_delta {x : E} (hx : x ∈ e.source) :
    compCLMOfOpenPartialHomeomorph e he he' hU hUΩ (delta (e x) : 𝓓'(Ω, ℝ)) =
      |(fderiv ℝ e x).det|⁻¹ • (delta x : 𝓓'(U, ℝ)) := by
  ext φ
  simp [pushforwardCLM_apply_of_mem_source φ hx]

/-- On the distribution of a function `f` locally integrable on `Ω`, the pullback along `e` is
the distribution of `f ∘ e`, for any additive Haar measure. -/
theorem compCLMOfOpenPartialHomeomorph_ofFun [MeasurableSpace E] [BorelSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → F} (hf : LocallyIntegrableOn f Ω μ) :
    compCLMOfOpenPartialHomeomorph e he he' hU hUΩ (ofFun Ω f μ ⊤) =
      ofFun U (fun x ↦ f (e x)) μ ⊤ := by
  have hdet (x : E) (hx : x ∈ (U : Set E)) : (fderiv ℝ e x).det ≠ 0 :=
    e.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) (hU hx)
  have hfe : LocallyIntegrableOn (fun x ↦ f (e x)) U μ :=
    hf.comp_contDiffOn_diffeo U.isOpen ((he.mono hU).of_le (by simp)) (e.injOn.mono hU) hdet hUΩ
  ext φ
  rw [compCLMOfOpenPartialHomeomorph_apply, ofFun_apply hf, ofFun_apply hfe,
    integral_pushforwardCLM_smul]

/-- The complex-linear extension of the pullback `e^* T` of a complex distribution pairs a
complex test function `φ` with `T` through `T (e_* φ)`. -/
theorem complexPairing_compCLMOfOpenPartialHomeomorph (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(U, ℂ)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).complexPairing φ =
      T.complexPairing (pushforwardCLM e he he' hU hUΩ φ) := by
  simp only [complexPairing_apply, compCLMOfOpenPartialHomeomorph_apply,
    postcompCLM_pushforwardCLM]

section Tempered

variable {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **Localized tempered comparison.** Let `Φ` be a bijection of `E` such that `Φ` and `Φ⁻¹` have
temperate growth, and which agrees with `e` on an open set `N ⊆ U`. If the test function `χ` equals
`1` on `e '' N`, then on `N` the pullback `e^* T` is the pullback `Φ^* (χ T)` of the tempered
distribution `χ T`. -/
theorem restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution {N : Opens E}
    (hNU : N ≤ U) {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth) (hΦe : EqOn Φ e N) (T : 𝓓'(Ω, ℂ))
    {χ : 𝓓(Ω, ℂ)} (hχ : EqOn χ 1 (e '' N)) :
    (restrictCLM (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) : 𝓓'(N, ℂ)) =
      TemperedDistribution.toDistribution N
        (TemperedDistribution.compCLM ℂ Φ hΦ hΨ (T.cutoffTempered χ)) := by
  ext φ
  rw [restrictCLM_apply, compCLMOfOpenPartialHomeomorph_apply,
    TemperedDistribution.toDistribution_apply, TemperedDistribution.compCLM_apply_apply,
    ← complexPairing_postcompCLM_ofRealCLM]
  refine (cutoffTempered_apply T χ fun y ↦ ?_).symm
  -- `φ` vanishes off `N`, and `Φ⁻¹ = e⁻¹` on the open set `e '' N`.
  have hφ (z : E) (hz : z ∉ (N : Set E)) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (φ.tsupport_subset h)
  have hNs : (N : Set E) ⊆ e.source := fun z hz ↦ hU (hNU hz)
  have hopen : IsOpen (e '' N) := (e.isOpen_image_iff_of_subset_source hNs).2 N.isOpen
  have hsymm : EqOn Φ.symm e.symm (e '' N) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [e.left_inv (hNs hz), Equiv.symm_apply_eq, hΦe hz]
  simp only [postcompCLM_apply, Function.comp_apply, Complex.ofRealCLM_apply,
    SchwartzMap.pushforwardCLM_apply, toSchwartzMapCLM_apply, smul_eq_mul]
  by_cases hy : y ∈ e '' N
  · obtain ⟨z, hz, rfl⟩ := hy
    have hev : (Φ.symm : E → E) =ᶠ[𝓝 (e z)] e.symm :=
      eventually_of_mem (hopen.mem_nhds ⟨z, hz, rfl⟩) hsymm
    have hd : fderiv ℝ Φ.symm (e z) = fderiv ℝ e.symm (e z) := hev.fderiv_eq
    rw [pushforwardCLM_apply_of_mem _ (e.map_source (hNs hz)), hχ ⟨z, hz, rfl⟩, hd,
      hsymm ⟨z, hz, rfl⟩]
    simp [hNU]
  · have h₁ : Φ.symm y ∉ (N : Set E) := fun h ↦ hy ⟨_, h, by rw [← hΦe h, Equiv.apply_symm_apply]⟩
    have h₂ : pushforwardCLM e he he' hU hUΩ (monoCLM ℝ φ) y = 0 := by
      by_cases hyt : y ∈ e.target
      · rw [pushforwardCLM_apply_of_mem _ hyt]
        have : e.symm y ∉ (N : Set E) := fun h ↦ hy ⟨_, h, e.right_inv hyt⟩
        simp [hNU, hφ _ this]
      · exact pushforwardCLM_apply_of_notMem _ hyt
    simp [h₂, hφ _ h₁]

end Tempered

end Distribution
