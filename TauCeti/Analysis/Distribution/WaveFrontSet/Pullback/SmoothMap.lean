/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.AddSnd
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Basic
public import TauCeti.Analysis.Distribution.WaveFrontSet.Submersion
import TauCeti.Analysis.Distribution.TestFunction.Convolution

/-!
# Pulling distributions back along smooth maps

Let `f : E → E'` be smooth on an open set `Ω` of a finite-dimensional real inner product space,
with values in an open set `Ω'`. The *normal set* of `f` consists of the covectors `(f x, η)` with
`η ≠ 0` and `Df(x)ᵀ η = 0`. If no covector of the wave front set of a complex distribution `T` on
`Ω'` lies in the normal set of `f`, then `T` has a pullback `f^* T` to `Ω`
(`Distribution.pullback`), which extends the composition of continuous functions with `f`
(`Distribution.pullback_ofFun`) and is linear in `T` (Hörmander I, Theorem 8.2.4). When `f` is a
submersion its normal set is empty, so every distribution has a pullback
(`Distribution.adjoint_fderiv_apply_ne_zero_of_surjective`), and it is the pullback by integration
over the fibres of `f` (`Distribution.pullback_eq_compCLMOfSubmersion`).

## The construction

Hörmander reduces the pullback along `f` to a pullback along a submersion followed by a
restriction. The map `g (x, y) = f x + y` (`TauCeti.addSnd`) on the open set
`W = {(x, y) | x ∈ Ω, f x + y ∈ Ω'}` of the Euclidean product `WithLp 2 (E × E')` is a submersion,
so every distribution on `Ω'` pulls back along `g` (`Distribution.compCLMOfSubmersion`), and the
wave front set pulls back with the transpose of the derivative
(`Distribution.waveFrontSet_compCLMOfSubmersion`). Since
`Dg(x, y)ᵀ η = (Df(x)ᵀ η, η)`, a covector of `WF(g^* T)` over `(x, 0)` is conormal to `E × {0}`
exactly when it comes from a covector of `WF(T)` in the normal set of `f`. So under the hypothesis
`g^* T` restricts to `E × {0}` (`Distribution.pullbackInl`), and `f = g ∘ (x ↦ (x, 0))` on `Ω`.
For a continuous function `F` both steps are composition with `F`, which gives `F ∘ f`.

When `f` is a submersion, the restriction to `E × {0}` is computed by pairing `g^* T` with the
test functions `(x, y) ↦ ψ x ρₙ y` for shrinking normalized bumps `ρₙ`
(`Distribution.tendsto_pullbackInl`). Their fibre integrals along `g` are the mollifications
`ρₙ ⋆ f_♯ ψ` of the fibre integral of `ψ` along `f`, which tend to `f_♯ ψ` as test functions.

## Main declarations

* `Distribution.pullback`: the pullback `f^* T` under the wave front hypothesis.
* `Distribution.pullback_ofFun`: for a continuous function `F` on `Ω'` satisfying the hypothesis,
  for instance a smooth one, `f^* F = F ∘ f`.
* `Distribution.pullback_eq_pullbackInl`: `f^* T` is the restriction to `E × {0}` of the pullback
  `Distribution.addSndPullback` of `T` along the submersion `TauCeti.addSnd`.
* `Distribution.pullback_add`, `Distribution.pullback_smul`,
  `Distribution.pullback_smul_of_ne_zero`, `Distribution.pullback_zero`,
  `Distribution.pullback_neg`, `Distribution.pullback_sub`: linearity in `T`.
* `Distribution.adjoint_fderiv_apply_ne_zero_of_surjective`: the hypothesis holds for every
  distribution when `f` is a submersion.
* `Distribution.pullback_eq_compCLMOfSubmersion`: along a submersion, `f^*` is the pullback
  `Distribution.compCLMOfSubmersion` by integration over the fibres.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 and its proof.
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, arXiv:1409.7662v2, Proposition 5.1.
-/

public section

noncomputable section

open Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory WithLp TauCeti
open scoped Distributions ContDiff Convolution Topology Pointwise

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'} {f : E → E'}

/-! ### The pullback along the submersion `(x, y) ↦ f x + y` -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']

/-- The pullback `T ↦ g^* T` along the submersion `g (x, y) = f x + y` (`TauCeti.addSnd`), by
integration over the fibres of `g`, as a continuous linear map. -/
def addSndPullback (hf : ContDiffOn ℝ ∞ f Ω) :
    𝓓'(Ω', ℂ) →L[ℝ] 𝓓'(addSndDomain hf.continuousOn Ω', ℂ) :=
  compCLMOfSubmersion volume volume (addSnd f) (contDiffOn_addSnd hf) (mapsTo_addSnd _)
    (surjective_fderiv_addSnd _ (hf.differentiableOn (by simp)))

/-- `g^*` is the pullback `Distribution.compCLMOfSubmersion` along `g`. -/
theorem addSndPullback_eq_compCLMOfSubmersion (hf : ContDiffOn ℝ ∞ f Ω) :
    addSndPullback (Ω' := Ω') hf = compCLMOfSubmersion volume volume (addSnd f)
      (contDiffOn_addSnd hf) (mapsTo_addSnd _)
      (surjective_fderiv_addSnd _ (hf.differentiableOn (by simp))) :=
  (rfl)

/-- `g^* T` pairs a test function `φ` with `T` through `T (g_♯ φ)`. -/
@[simp]
theorem addSndPullback_apply (hf : ContDiffOn ℝ ∞ f Ω) (T : 𝓓'(Ω', ℂ))
    (φ : 𝓓(addSndDomain hf.continuousOn Ω', ℝ)) :
    addSndPullback hf T φ = T (fiberIntegralCLM volume volume (addSnd f) (contDiffOn_addSnd hf)
      (mapsTo_addSnd _) (surjective_fderiv_addSnd _ (hf.differentiableOn (by simp))) φ) := by
  rw [addSndPullback_eq_compCLMOfSubmersion, compCLMOfSubmersion_apply]

/-- The pullback `g^* T` is homogeneous in `T`. -/
@[simp]
theorem addSndPullback_smul (hf : ContDiffOn ℝ ∞ f Ω) (c : ℂ) (T : 𝓓'(Ω', ℂ)) :
    addSndPullback hf (c • T) = c • addSndPullback hf T := by
  ext φ
  simp

/-- **The wave front set of `g^* T` over `E × {0}`.** If no covector of `WF(T)` lies in the
normal set of `f`, then no covector of `WF(g^* T)` over `Ω × {0}` is conormal to `E × {0}`. -/
theorem notMem_waveFrontSet_addSndPullback (hf : ContDiffOn ℝ ∞ f Ω) {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    ∀ x ∈ Ω, ∀ η : E', η ≠ 0 →
      (toLp 2 (x, (0 : E')), toLp 2 ((0 : E), η)) ∉ (addSndPullback hf T).waveFrontSet := by
  intro x hx η' _ hmem
  rw [addSndPullback_eq_compCLMOfSubmersion, waveFrontSet_compCLMOfSubmersion] at hmem
  obtain ⟨-, η, hη, hadj⟩ := hmem
  dsimp only at hη hadj
  rw [adjoint_fderiv_addSnd_apply (p := toLp 2 (x, 0))
    ((hf.differentiableOn (by simp) x hx).differentiableAt (Ω.isOpen.mem_nhds hx))] at hadj
  have hfst := congrArg WithLp.fst hadj
  simp only [toLp_fst] at hfst
  exact h x hx η (by simpa using hη) hfst

/-! ### The pullback -/

/-- **The pullback of a distribution along a smooth map** (Hörmander I, Theorem 8.2.4). Let `f` be
smooth on `Ω` and map `Ω` into `Ω'`, and let `T` be a complex distribution on `Ω'` such that no
covector `(f x, η)` of the wave front set of `T` with `x ∈ Ω` satisfies `Df(x)ᵀ η = 0`, that is,
the wave front set of `T` does not meet the normal set of `f`. Then `f^* T` is the distribution on
`Ω` obtained by pulling `T` back along the submersion `(x, y) ↦ f x + y` and restricting the result
to `E × {0}`. On a continuous function `F` it is `F ∘ f` (`Distribution.pullback_ofFun`). -/
def pullback (T : 𝓓'(Ω', ℂ)) (f : E → E') (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    𝓓'(Ω, ℂ) :=
  (addSndPullback hf T).pullbackInl (mapsTo_inl_addSndDomain hf.continuousOn hfΩ)
    (notMem_waveFrontSet_addSndPullback hf h)

/-- **The pullback as a restriction.** `f^* T` is the restriction `Distribution.pullbackInl` to
`E × {0}` of the pullback `g^* T` along the submersion `g (x, y) = f x + y`
(`Distribution.addSndPullback`). The statement takes any `S` equal to `g^* T`, together with its
wave front hypothesis, so that it can be used after rewriting `g^* T`. -/
theorem pullback_eq_pullbackInl (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0)
    {S : 𝓓'(addSndDomain hf.continuousOn Ω', ℂ)} (hTS : addSndPullback hf T = S)
    (hS : ∀ x ∈ Ω, ∀ η : E', η ≠ 0 →
      (toLp 2 (x, (0 : E')), toLp 2 ((0 : E), η)) ∉ S.waveFrontSet) :
    T.pullback f hf hfΩ h = S.pullbackInl (mapsTo_inl_addSndDomain hf.continuousOn hfΩ) hS := by
  subst hTS
  rfl

/-- **Agreement with composition.** For a function `F` continuous on `Ω'` whose wave front set
does not meet the normal set of `f`, the pullback of `F` along `f` is the function `F ∘ f`. This
applies in particular to every `F` smooth on `Ω'`, whose wave front set is empty
(`Distribution.waveFrontSet_ofFun_eq_empty`). -/
theorem pullback_ofFun (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') {F : E' → ℂ}
    (hF : ContinuousOn F Ω')
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ (ofFun Ω' F volume ⊤).waveFrontSet →
      (fderiv ℝ f x).adjoint η ≠ 0) :
    (ofFun Ω' F volume ⊤).pullback f hf hfΩ h = ofFun Ω (fun x ↦ F (f x)) volume ⊤ := by
  have hg : addSndPullback hf (ofFun Ω' F volume ⊤) =
      ofFun (addSndDomain hf.continuousOn Ω') (fun p ↦ F (addSnd f p)) volume ⊤ :=
    compCLMOfSubmersion_ofFun volume volume _ _ _ hF
  have hFg : ContinuousOn (fun p ↦ F (addSnd f p)) (addSndDomain hf.continuousOn Ω') :=
    hF.comp (contDiffOn_addSnd hf).continuousOn (mapsTo_addSnd _)
  rw [pullback_eq_pullbackInl hf hfΩ h hg (hg ▸ notMem_waveFrontSet_addSndPullback hf h),
    pullbackInl_ofFun _ hFg]
  simp

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
/-- The hypothesis of `Distribution.pullback` holds for every distribution when `f` is a
submersion: the transpose of a surjective linear map is injective, so the normal set of `f` is
empty. -/
theorem adjoint_fderiv_apply_ne_zero_of_surjective
    (hsurj : ∀ x ∈ Ω, Surjective (fderiv ℝ f x)) (T : 𝓓'(Ω', ℂ)) :
    ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0 := fun x hx _ hη h0 ↦
  (mem_waveFrontSet_iff.1 hη).2.1 <| (ContinuousLinearMap.adjoint_injective_iff_denseRange.2
    (hsurj x hx).denseRange) (h0.trans (map_zero _).symm)

/-! ### Linearity -/

/-- **Additivity of the pullback in the distribution.** -/
theorem pullback_add (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') {S T : 𝓓'(Ω', ℂ)}
    (hS : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ S.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0)
    (hT : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (S + T).pullback f hf hfΩ (fun x hx η hm ↦
      (waveFrontSet_add_subset S T hm).elim (hS x hx η) (hT x hx η)) =
      S.pullback f hf hfΩ hS + T.pullback f hf hfΩ hT := by
  have hS' := notMem_waveFrontSet_addSndPullback hf hS
  have hT' := notMem_waveFrontSet_addSndPullback hf hT
  rw [pullback_eq_pullbackInl hf hfΩ hS rfl hS', pullback_eq_pullbackInl hf hfΩ hT rfl hT']
  exact (pullback_eq_pullbackInl hf hfΩ _ (map_add _ S T) _).trans (pullbackInl_add _ hS' hT')

/-- **Homogeneity of the pullback in the distribution.** -/
theorem pullback_smul (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') (c : ℂ) {T : 𝓓'(Ω', ℂ)}
    (hT : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (c • T).pullback f hf hfΩ (fun x hx η hm ↦ hT x hx η (waveFrontSet_smul_subset c T hm)) =
      c • T.pullback f hf hfΩ hT := by
  have hT' := notMem_waveFrontSet_addSndPullback hf hT
  rw [pullback_eq_pullbackInl hf hfΩ hT rfl hT']
  exact (pullback_eq_pullbackInl hf hfΩ _ (addSndPullback_smul hf c T) _).trans
    (pullbackInl_smul _ c hT')

/-- **Homogeneity of the pullback in the distribution**, for a nonzero scalar `c`, with the
hypothesis on the wave front set stated for `c • T`. -/
@[simp]
theorem pullback_smul_of_ne_zero (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') {c : ℂ}
    (hc : c ≠ 0) {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ (c • T).waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (c • T).pullback f hf hfΩ h = c • T.pullback f hf hfΩ (fun x hx η hm ↦
      h x hx η ((waveFrontSet_smul hc T).symm.subset hm)) :=
  pullback_smul hf hfΩ c _

/-- The pullback of the zero distribution is zero. -/
@[simp]
theorem pullback_zero (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') :
    (0 : 𝓓'(Ω', ℂ)).pullback f hf hfΩ
      (fun _ _ _ hm ↦ absurd (waveFrontSet_zero.subset hm) (notMem_empty _)) = 0 :=
  (pullback_eq_pullbackInl hf hfΩ _ (map_zero _) _).trans (pullbackInl_zero _)

/-- The pullback commutes with negation of the distribution. -/
@[simp]
theorem pullback_neg (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ (-T).waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (-T).pullback f hf hfΩ h = -T.pullback f hf hfΩ (fun x hx η hm ↦
      h x hx η ((waveFrontSet_neg T).symm.subset hm)) := by
  have hT' := notMem_waveFrontSet_addSndPullback hf (T := T) fun x hx η hm ↦
    h x hx η ((waveFrontSet_neg T).symm.subset hm)
  rw [pullback_eq_pullbackInl hf hfΩ _ rfl hT']
  exact (pullback_eq_pullbackInl hf hfΩ _ (map_neg _ T) _).trans
    (pullbackInl_neg _ fun x hx η hη hm ↦ hT' x hx η hη ((waveFrontSet_neg _).subset hm))

/-- The pullback commutes with subtraction of distributions. -/
theorem pullback_sub (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') {S T : 𝓓'(Ω', ℂ)}
    (hS : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ S.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0)
    (hT : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (S - T).pullback f hf hfΩ (fun x hx η hm ↦
      (waveFrontSet_sub_subset S T hm).elim (hS x hx η) (hT x hx η)) =
      S.pullback f hf hfΩ hS - T.pullback f hf hfΩ hT := by
  have hS' := notMem_waveFrontSet_addSndPullback hf hS
  have hT' := notMem_waveFrontSet_addSndPullback hf hT
  rw [pullback_eq_pullbackInl hf hfΩ hS rfl hS', pullback_eq_pullbackInl hf hfΩ hT rfl hT']
  exact (pullback_eq_pullbackInl hf hfΩ _ (map_sub _ S T) _).trans (pullbackInl_sub _ hS' hT')

/-! ### Agreement with the pullback along a submersion -/

section Submersion

/-- Mollifying the fibre integral `f_♯ ψ` by the normalized bump `ρ` of `σ` gives
`z ↦ ∫ ψ(x) ρ(z - f x) dx`. -/
private theorem mollify_fiberIntegralCLM_apply (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    (hsurj : ∀ x ∈ Ω, Surjective (fderiv ℝ f x)) (ψ : 𝓓(Ω, ℝ)) (σ : ContDiffBump (0 : E'))
    (hσ : closedBall (0 : E') σ.rOut +
      tsupport (fiberIntegralCLM volume volume f hf hfΩ hsurj ψ) ⊆ (Ω' : Set E')) (z : E') :
    mollify (fiberIntegralCLM volume volume f hf hfΩ hsurj ψ) volume σ hσ z =
      ∫ x, ψ x * σ.normed volume (z - f x) := by
  have h := integral_fiberIntegralCLM_smul volume volume hf hfΩ hsurj ψ
    (g := fun w ↦ σ.normed volume (z - w))
    (σ.continuous_normed.comp (continuous_const.sub continuous_id)).continuousOn
  simp only [smul_eq_mul] at h
  rw [mollify_apply, convolution_eq_swap, ← h]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]

/-- The integrand `(z, x) ↦ ψ(x) ρ(z - f x) h(z)` of the mollified fibre integral is integrable. -/
private theorem integrable_uncurry_mul_sub (hf : ContinuousOn f Ω) (ψ : 𝓓(Ω, ℝ))
    (σ : ContDiffBump (0 : E')) {h : E' → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable (uncurry fun z x ↦ ψ x * σ.normed volume (z - f x) * h z)
      (volume.prod volume) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro
    (hhc.isCompact.prod ψ.hasCompactSupport.isCompact) fun q hq ↦ ?_)
  · refine Continuous.mul (ContinuousOn.continuous_of_tsupport_subset ?_
      (Ω.isOpen.preimage continuous_snd) (tsupport_mul_subset_left.trans
        ((tsupport_comp_subset_preimage ψ continuous_snd).trans
          (preimage_mono ψ.tsupport_subset)))) (hh.comp continuous_fst)
    exact (ψ.continuous.comp continuous_snd).continuousOn.mul
      (σ.continuous_normed.comp_continuousOn (continuous_fst.continuousOn.sub
        (hf.comp continuous_snd.continuousOn (mapsTo_preimage _ _))))
  · rcases not_and_or.1 hq with hq | hq
    · simp [uncurry, image_eq_zero_of_notMem_tsupport hq]
    · simp [uncurry, image_eq_zero_of_notMem_tsupport hq]

/-- The integrand `(x, y) ↦ ψ(x) ρ(y) h(f x + y)` of the fibre integral along `g` is integrable. -/
private theorem integrable_mul_add (hf : ContinuousOn f Ω) (ψ : 𝓓(Ω, ℝ))
    (σ : ContDiffBump (0 : E')) {h : E' → ℝ} (hh : Continuous h) :
    Integrable (fun q : E × E' ↦ ψ q.1 * σ.normed volume q.2 * h (f q.1 + q.2))
      (volume.prod volume) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro
    (ψ.hasCompactSupport.isCompact.prod (isCompact_closedBall (0 : E') σ.rOut)) fun q hq ↦ ?_)
  · refine ContinuousOn.continuous_of_tsupport_subset ?_ (Ω.isOpen.preimage continuous_fst)
      (tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans
        ((tsupport_comp_subset_preimage ψ continuous_fst).trans
          (preimage_mono ψ.tsupport_subset))))
    exact ((ψ.continuous.comp continuous_fst).mul (σ.continuous_normed.comp
      continuous_snd)).continuousOn.mul (hh.comp_continuousOn
        ((hf.comp continuous_fst.continuousOn (mapsTo_preimage _ _)).add
          continuous_snd.continuousOn))
  · rcases not_and_or.1 hq with hq | hq
    · simp [image_eq_zero_of_notMem_tsupport hq]
    · have hρ : σ.normed volume q.2 = 0 := notMem_support.1 fun h ↦ hq (ball_subset_closedBall
        ((σ.support_normed_eq (μ := volume)).subset h))
      simp [hρ]

/-- **The fibre integral of `ψ ⊗ ρ` along `g`** is the mollification of `f_♯ ψ` by `ρ`: both are
`z ↦ ∫ ψ(x) ρ(z - f x) dx`. -/
private theorem fiberIntegralCLM_eq_mollify (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    (hsurj : ∀ x ∈ Ω, Surjective (fderiv ℝ f x)) (ψ : 𝓓(Ω, ℝ)) (σ : ContDiffBump (0 : E'))
    {F : 𝓓(addSndDomain hf.continuousOn Ω', ℝ)} (hF : ∀ p, F p = ψ p.fst * σ.normed volume p.snd)
    (hσ : closedBall (0 : E') σ.rOut +
      tsupport (fiberIntegralCLM volume volume f hf hfΩ hsurj ψ) ⊆ (Ω' : Set E')) :
    fiberIntegralCLM volume volume (addSnd f) (contDiffOn_addSnd hf) (mapsTo_addSnd _)
        (surjective_fderiv_addSnd _ (hf.differentiableOn (by simp))) F =
      mollify (fiberIntegralCLM volume volume f hf hfΩ hsurj ψ) volume σ hσ := by
  set ρ := σ.normed volume
  refine ((eq_fiberIntegralCLM_iff volume volume _ _ _).2 fun h hh hhc _ ↦ ?_).symm
  -- Both sides are `∫ x, ∫ z, ψ x * ρ (z - f x) * h z`.
  have hint₁ := integrable_uncurry_mul_sub hf.continuousOn ψ σ hh.continuous hhc
  have hint₂ := integrable_mul_add hf.continuousOn ψ σ hh.continuous
  simp_rw [mollify_fiberIntegralCLM_apply hf hfΩ hsurj ψ σ hσ, smul_eq_mul, ← integral_mul_const,
    hF, addSnd_apply]
  rw [integral_integral_swap hint₁,
    ← (volume_preserving_symm_measurableEquiv_toLp_prod E E').symm.integral_comp']
  simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, toLp_fst, toLp_snd]
  rw [Measure.volume_eq_prod, integral_prod _ hint₂]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  conv_rhs => rw [← integral_sub_right_eq_self _ (f x)]
  simp only [add_sub_cancel]

/-- **Agreement with the pullback along a submersion.** When `f` is a submersion, every
distribution `T` satisfies the hypothesis of `Distribution.pullback`
(`Distribution.adjoint_fderiv_apply_ne_zero_of_surjective`), and `f^* T` is the distribution
`Distribution.compCLMOfSubmersion`, defined by integration over the fibres of `f`. -/
theorem pullback_eq_compCLMOfSubmersion (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    (hsurj : ∀ x ∈ Ω, Surjective (fderiv ℝ f x)) (T : 𝓓'(Ω', ℂ)) :
    T.pullback f hf hfΩ (adjoint_fderiv_apply_ne_zero_of_surjective hsurj T) =
      compCLMOfSubmersion volume volume f hf hfΩ hsurj T := by
  ext ψ
  -- Test functions `ψ ⊗ ρ n` on `W` for normalized bumps `ρ n` of radii shrinking to `0`.
  have hU := mapsTo_inl_addSndDomain hf.continuousOn hfΩ
  obtain ⟨σ, F, hσ0, hσW, hF⟩ := exists_seq_tensor_mollifier hU ψ
  have hσφ (n : ℕ) : closedBall (0 : E') (σ n).rOut +
      tsupport (fiberIntegralCLM volume volume f hf hfΩ hsurj ψ) ⊆ (Ω' : Set E') := by
    rintro _ ⟨y, hy, w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := tsupport_fiberIntegralCLM_subset volume volume hf hfΩ hsurj ψ hw
    simpa [add_comm] using (mem_addSndDomain.1 (hσW n x hx y hy)).2
  -- The values of `g^* T` at `ψ ⊗ ρ n` tend both to the pullback at `ψ` and to `T (f_♯ ψ)`.
  have hT := notMem_waveFrontSet_addSndPullback hf
    (adjoint_fderiv_apply_ne_zero_of_surjective hsurj T)
  have h₁ := tendsto_pullbackInl (addSndPullback hf T) hU hT ψ (l := atTop)
    (ρ := fun n ↦ (σ n).normed volume) (r := fun n ↦ (σ n).rOut) (M := 1) (f := F)
    (Eventually.of_forall fun n ↦ by
      simp_rw [abs_of_nonneg ((σ n).nonneg_normed _), (σ n).integral_normed, le_refl])
    (by simp_rw [ContDiffBump.integral_normed, tendsto_const_nhds])
    (Eventually.of_forall fun n ↦ by
      simpa only [(σ n).support_normed_eq] using ball_subset_closedBall)
    hσ0 (Eventually.of_forall hF)
  have h₂ : Tendsto (fun n ↦ addSndPullback hf T (F n)) atTop
      (𝓝 (compCLMOfSubmersion volume volume f hf hfΩ hsurj T ψ)) := by
    rw [compCLMOfSubmersion_apply]
    refine (((map_continuous T).tendsto _).comp (tendsto_mollify _ volume hσ0 hσφ)).congr
      fun n ↦ ?_
    rw [Function.comp_apply, addSndPullback_apply,
      fiberIntegralCLM_eq_mollify hf hfΩ hsurj ψ (σ n) (hF n) (hσφ n)]
  rw [pullback_eq_pullbackInl hf hfΩ _ rfl hT]
  exact tendsto_nhds_unique h₁ h₂

end Submersion

end Distribution
