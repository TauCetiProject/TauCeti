/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.AddSnd
public import TauCeti.Analysis.Distribution.TestFunction.Convolution
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Basic
public import TauCeti.Analysis.Distribution.WaveFrontSet.Submersion

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

The wave front set of the pullback lies in the pullback of the wave front set of `T`
(`Distribution.waveFrontSet_pullback_subset`):

`WF(f^* T) ⊆ {(x, Df(x)ᵀ η) | (f x, η) ∈ WF(T)}`.

So `k^* (f^* T)` is defined whenever the wave front set of `T` meets neither the normal set of `f`
nor that of `f ∘ k` (`Distribution.adjoint_fderiv_apply_ne_zero_of_comp`).

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
The wave front set bound composes the bounds for the two steps
(`Distribution.waveFrontSet_compCLMOfSubmersion`, `Distribution.waveFrontSet_pullbackInl_subset`):
a covector `((x, 0), (ξ, η))` of `WF(g^* T)` has `η` with `(f x, η) ∈ WF(T)` and
`ξ = Df(x)ᵀ η`.

When `f` is a submersion, the restriction to `E × {0}` is computed by pairing `g^* T` with the
test functions `(x, y) ↦ ψ x ρₙ y` for shrinking normalized bumps `ρₙ`
(`Distribution.tendsto_pullbackInl`). Their fibre integrals along `g` are the mollifications
`ρₙ ⋆ f_♯ ψ` of the fibre integral of `ψ` along `f`, which tend to `f_♯ ψ` as test functions.

## Composition and locality

The same test functions give the functoriality of the pullback with respect to a submersion `k`
from an open set `Ω₀` into `Ω`: `(f ∘ k)^* T = k^* (f^* T)`, where `k^*` is the pullback by
integration over the fibres of `k`. Pairing `(f ∘ k)^* T` with `ψ ⊗ ρₙ` and `f^* T` with
`k_♯ ψ ⊗ ρₙ`, for the same bumps `ρₙ`, the fibre integrals of these two test functions along
`(w, y) ↦ f (k w) + y` and `(x, y) ↦ f x + y` coincide: both pair a test function `u` with
`∫ ψ(w) ∫ ρₙ(y) u(f (k w) + y) dy dw`, by Fubini's theorem and the defining identity of `k_♯`.
Taking for `k` the inclusion of an open set `U ≤ Ω`, along which the pullback is the restriction to
`U` (`Distribution.compCLMOfSubmersion_id`), shows that `f^* T` restricts to the pullback along `f`
on `U`. Locality in the target is the same comparison for `ψ ⊗ ρₙ` on the two domains
`{(x, y) | f x + y ∈ Ω''}` and `{(x, y) | f x + y ∈ Ω'}`. These results give locality and
invariance under changes of coordinates in the source only; changes of coordinates in the target
need composition with maps that are not submersions, which is
`Distribution.pullback_eq_pullback_compCLMOfSubmersion` in
`TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Comp`.

## Main declarations

* `Distribution.pullback`: the pullback `f^* T` under the wave front hypothesis.
* `Distribution.pullback_ofFun`: for a continuous function `F` on `Ω'` satisfying the hypothesis,
  for instance a smooth one, `f^* F = F ∘ f`.
* `Distribution.pullback_eq_pullbackInl`: `f^* T` is the restriction to `E × {0}` of the pullback
  `Distribution.addSndPullback` of `T` along the submersion `TauCeti.addSnd`.
* `Distribution.pullback_add`, `Distribution.pullback_smul`,
  `Distribution.pullback_smul_of_ne_zero`, `Distribution.pullback_zero`,
  `Distribution.pullback_neg`, `Distribution.pullback_sub`: linearity in `T`.
* `Distribution.isMicrolocallySmoothAt_pullback`, `Distribution.waveFrontSet_pullback_subset`:
  the wave front set of `f^* T` lies in `{(x, Df(x)ᵀ η) | (f x, η) ∈ WF(T)}`.
* `Distribution.adjoint_fderiv_apply_ne_zero_of_comp`: if `WF(T)` meets neither the normal set
  of `f` nor that of `f ∘ k`, then `WF(f^* T)` does not meet the normal set of `k`.
* `Distribution.adjoint_fderiv_apply_ne_zero_of_surjective`: the hypothesis holds for every
  distribution when `f` is a submersion.
* `Distribution.tendsto_addSndPullback_pullback`: `f^* T ψ` is the limit of the values of the
  pullback along `(x, y) ↦ f x + y` at `ψ ⊗ ρₙ`, for normalized bumps `ρₙ` of radii tending to zero.
* `Distribution.mollify_fiberIntegralCLM_apply`: the mollification of the fibre integral `f_♯ ψ`
  by a normalized bump `ρ` is `z ↦ ∫ ψ(x) ρ(z - f x) dx`.
* `Distribution.pullback_eq_compCLMOfSubmersion`: along a submersion, `f^*` is the pullback
  `Distribution.compCLMOfSubmersion` by integration over the fibres.
* `Distribution.pullback_eq_compCLMOfSubmersion_pullback`,
  `Distribution.pullback_comp_of_surjective`: for a submersion `k`, `(f ∘ k)^* T = k^* (f^* T)`.
* `Distribution.adjoint_fderiv_apply_ne_zero_comp_of_surjective`: for a submersion `k`, the
  hypothesis for `f` gives the hypothesis for `f ∘ k`.
* `Distribution.restrictCLM_pullback`, `Distribution.pullback_restrictCLM`,
  `Distribution.pullback_congr`: the pullback is local in the source and in the target, and only
  depends on `f` on `Ω`.

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

/-! ### The wave front set of the pullback -/

/-- **The wave front set of the pullback, pointwise** (Hörmander I, Theorem 8.2.4). Let `x₀ ∈ Ω`
and `ξ₀ ≠ 0`. If `T` is microlocally smooth at `(f x₀, η)` for every `η` with
`Df(x₀)ᵀ η = ξ₀`, then `f^* T` is microlocally smooth at `(x₀, ξ₀)`. -/
theorem isMicrolocallySmoothAt_pullback (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) {x₀ ξ₀ : E}
    (hx₀ : x₀ ∈ Ω) (hξ₀ : ξ₀ ≠ 0)
    (hT : ∀ η, (fderiv ℝ f x₀).adjoint η = ξ₀ → T.IsMicrolocallySmoothAt (f x₀) η) :
    (T.pullback f hf hfΩ h).IsMicrolocallySmoothAt x₀ ξ₀ := by
  have hS := notMem_waveFrontSet_addSndPullback hf h
  have hU := mapsTo_inl_addSndDomain hf.continuousOn hfΩ
  rw [pullback_eq_pullbackInl hf hfΩ h rfl hS]
  refine isMicrolocallySmoothAt_pullbackInl _ hU hS hx₀ hξ₀ fun η ↦ ?_
  have hd : DifferentiableAt ℝ f (toLp 2 (x₀, (0 : E'))).fst :=
    (hf.differentiableOn (by simp) x₀ hx₀).differentiableAt (Ω.isOpen.mem_nhds hx₀)
  rw [addSndPullback_eq_compCLMOfSubmersion, isMicrolocallySmoothAt_compCLMOfSubmersion_iff
    volume volume _ _ _ T (hU hx₀) fun h0 ↦ hξ₀ (by simpa using congrArg WithLp.fst h0)]
  intro η' hη'
  rw [adjoint_fderiv_addSnd_apply hd] at hη'
  obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 (toLp_injective 2 hη')
  simpa [addSnd_apply] using hT η' h₁

/-- **The wave front set of the pullback** (Hörmander I, Theorem 8.2.4). The covectors of the
wave front set of `f^* T` are of the form `(x, Df(x)ᵀ η)` with `x ∈ Ω` and `(f x, η)` in the wave
front set of `T`:

`WF(f^* T) ⊆ {(x, Df(x)ᵀ η) | (f x, η) ∈ WF(T)}`.

Covectors with `Df(x)ᵀ η = 0` do not occur, by the hypothesis on `WF(T)`. For a submersion this
is an equality (`Distribution.pullback_eq_compCLMOfSubmersion`,
`Distribution.waveFrontSet_compCLMOfSubmersion`). -/
theorem waveFrontSet_pullback_subset (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (T.pullback f hf hfΩ h).waveFrontSet ⊆
      {p | p.1 ∈ Ω ∧ ∃ η, (f p.1, η) ∈ T.waveFrontSet ∧ (fderiv ℝ f p.1).adjoint η = p.2} := by
  rintro ⟨x, ξ⟩ hxξ
  obtain ⟨hx, hξ, hns⟩ := mem_waveFrontSet_iff.1 hxξ
  refine ⟨hx, ?_⟩
  by_contra hmem
  refine hns (isMicrolocallySmoothAt_pullback hf hfΩ h hx hξ fun η hη ↦ ?_)
  by_contra hns'
  refine hmem ⟨η, mem_waveFrontSet_iff.2 ⟨hfΩ hx, ?_, hns'⟩, hη⟩
  rintro rfl
  exact hξ (by rw [← hη, map_zero])

/-- **Pulling back twice.** Let `k` be differentiable on an open set `Ω₀` with values in `Ω`, and
let the wave front set of `T` not meet the normal set of `f`. If it does not meet the normal set
of `f ∘ k` either, then the wave front set of `f^* T` does not meet the normal set of `k`, so
that, for `k` smooth, `k^* (f^* T)` is defined. -/
theorem adjoint_fderiv_apply_ne_zero_of_comp {E₀ : Type*} [NormedAddCommGroup E₀]
    [InnerProductSpace ℝ E₀] [CompleteSpace E₀] {Ω₀ : Opens E₀} {k : E₀ → E}
    (hk : DifferentiableOn ℝ k Ω₀) (hkΩ : MapsTo k Ω₀ Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hfΩ : MapsTo f Ω Ω') {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0)
    (hfk : ∀ x ∈ Ω₀, ∀ η, ((f ∘ k) x, η) ∈ T.waveFrontSet →
      (fderiv ℝ (f ∘ k) x).adjoint η ≠ 0) :
    ∀ x ∈ Ω₀, ∀ ζ, (k x, ζ) ∈ (T.pullback f hf hfΩ h).waveFrontSet →
      (fderiv ℝ k x).adjoint ζ ≠ 0 := by
  intro x hx ζ hζ
  obtain ⟨-, η, hη, hηζ⟩ := waveFrontSet_pullback_subset hf hfΩ h hζ
  dsimp only at hη hηζ
  subst hηζ
  have hkx : DifferentiableAt ℝ k x := (hk x hx).differentiableAt (Ω₀.isOpen.mem_nhds hx)
  have hfkx : DifferentiableAt ℝ f (k x) :=
    (hf.differentiableOn (by simp) _ (hkΩ hx)).differentiableAt (Ω.isOpen.mem_nhds (hkΩ hx))
  have hne := hfk x hx η hη
  rwa [fderiv_comp x hfkx hkx, ContinuousLinearMap.adjoint_comp] at hne

/-! ### Agreement with the pullback along a submersion -/

section Submersion

/-- The values `g^* T (ψ ⊗ ρₙ)` of the pullback along `g (x, y) = f x + y` at the tensor products of
`ψ` with normalized bumps `ρₙ` of radii tending to zero tend to `f^* T ψ`. -/
theorem tendsto_addSndPullback_pullback (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) (ψ : 𝓓(Ω, ℝ))
    {σ : ℕ → ContDiffBump (0 : E')} (hσ0 : Tendsto (fun n ↦ (σ n).rOut) atTop (𝓝 0))
    {G : ℕ → 𝓓(addSndDomain hf.continuousOn Ω', ℝ)}
    (hG : ∀ n p, G n p = ψ p.fst * (σ n).normed volume p.snd) :
    Tendsto (fun n ↦ addSndPullback hf T (G n)) atTop (𝓝 (T.pullback f hf hfΩ h ψ)) := by
  rw [pullback_eq_pullbackInl hf hfΩ h rfl (notMem_waveFrontSet_addSndPullback hf h)]
  exact tendsto_pullbackInl_bump _ (mapsTo_inl_addSndDomain hf.continuousOn hfΩ) _ ψ hσ0
    (Eventually.of_forall hG)

/-- Mollifying the fibre integral `f_♯ ψ` by the normalized bump `ρ` of `σ` gives
`z ↦ ∫ ψ(x) ρ(z - f x) dx`. -/
theorem mollify_fiberIntegralCLM_apply (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
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
  · rw [mul_normed_eq_zero_of_notMem ψ σ hq, zero_mul]

/-- **Fubini for tensor products.** Integrating `(x, y) ↦ ψ(x) ρ(y) u(f x + y)` first in `y`. -/
private theorem integral_mul_addSnd_eq (hf : ContinuousOn f Ω) (ψ : 𝓓(Ω, ℝ))
    (σ : ContDiffBump (0 : E')) {u : E' → ℝ} (hu : Continuous u) :
    ∫ p : WithLp 2 (E × E'), ψ p.fst * σ.normed volume p.snd * u (f p.fst + p.snd) =
      ∫ x, ψ x * ∫ y, σ.normed volume y * u (f x + y) := by
  rw [← (volume_preserving_symm_measurableEquiv_toLp_prod E E').symm.integral_comp']
  simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, toLp_fst, toLp_snd]
  rw [Measure.volume_eq_prod, integral_prod _ (integrable_mul_add hf ψ σ hu)]
  simp only [← integral_const_mul, mul_assoc]

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
  simp_rw [mollify_fiberIntegralCLM_apply hf hfΩ hsurj ψ σ hσ, smul_eq_mul, ← integral_mul_const,
    hF, addSnd_apply]
  rw [integral_integral_swap hint₁, integral_mul_addSnd_eq hf.continuousOn ψ σ hh.continuous]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  conv_rhs => rw [← integral_sub_right_eq_self _ (f x)]
  simp only [add_sub_cancel, ← integral_const_mul, mul_assoc]

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
  have h₁ := tendsto_addSndPullback_pullback hf hfΩ
    (adjoint_fderiv_apply_ne_zero_of_surjective hsurj T) ψ hσ0 hF
  have h₂ : Tendsto (fun n ↦ addSndPullback hf T (F n)) atTop
      (𝓝 (compCLMOfSubmersion volume volume f hf hfΩ hsurj T ψ)) := by
    rw [compCLMOfSubmersion_apply]
    refine (((map_continuous T).tendsto _).comp (tendsto_mollify _ volume hσ0 hσφ)).congr
      fun n ↦ ?_
    rw [Function.comp_apply, addSndPullback_apply,
      fiberIntegralCLM_eq_mollify hf hfΩ hsurj ψ (σ n) (hF n) (hσφ n)]
  exact tendsto_nhds_unique h₁ h₂

end Submersion

/-! ### Composition with submersions and locality -/

section Comp

variable {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [MeasurableSpace E₀] [BorelSpace E₀] {Ω₀ : Opens E₀} {k : E₀ → E}

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E']
  [BorelSpace E'] [MeasurableSpace E₀] [BorelSpace E₀] in
/-- If the wave front set of `T` does not meet the normal set of `f`, then it does not meet the
normal set of `f ∘ k` for a submersion `k` either, since the transpose of `Dk(x)` is injective. -/
theorem adjoint_fderiv_apply_ne_zero_comp_of_surjective [CompleteSpace E₀]
    (hf : DifferentiableOn ℝ f Ω) (hk : DifferentiableOn ℝ k Ω₀) (hkΩ : MapsTo k Ω₀ Ω)
    (hksurj : ∀ x ∈ Ω₀, Surjective (fderiv ℝ k x)) {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    ∀ x ∈ Ω₀, ∀ η, ((f ∘ k) x, η) ∈ T.waveFrontSet → (fderiv ℝ (f ∘ k) x).adjoint η ≠ 0 := by
  intro x hx η hη h0
  have hkx : DifferentiableAt ℝ k x := (hk x hx).differentiableAt (Ω₀.isOpen.mem_nhds hx)
  have hfkx : DifferentiableAt ℝ f (k x) :=
    (hf _ (hkΩ hx)).differentiableAt (Ω.isOpen.mem_nhds (hkΩ hx))
  rw [fderiv_comp x hfkx hkx, ContinuousLinearMap.adjoint_comp] at h0
  exact h (k x) (hkΩ hx) η hη <| (ContinuousLinearMap.adjoint_injective_iff_denseRange.2
    (hksurj x hx).denseRange) (h0.trans (map_zero _).symm)

/-- **Pulling back along a submersion after a smooth map.** Let `k` be a submersion from `Ω₀`
into `Ω`, and let `g` be smooth on `Ω₀`, with values in `Ω'`, and equal to `f ∘ k` there. If the
wave front set of `T` meets neither the normal set of `f` nor that of `g`, then the pullback of `T`
along `g` is the pullback of `f^* T` along `k` by integration over the fibres of `k`:
`g^* T = k^* (f^* T)`. -/
theorem pullback_eq_compCLMOfSubmersion_pullback (hf : ContDiffOn ℝ ∞ f Ω)
    (hfΩ : MapsTo f Ω Ω') (hk : ContDiffOn ℝ ∞ k Ω₀) (hkΩ : MapsTo k Ω₀ Ω)
    (hksurj : ∀ x ∈ Ω₀, Surjective (fderiv ℝ k x)) {g : E₀ → E'} (hg : ContDiffOn ℝ ∞ g Ω₀)
    (hgΩ : MapsTo g Ω₀ Ω') (hgfk : EqOn g (f ∘ k) Ω₀) {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0)
    (hT : ∀ x ∈ Ω₀, ∀ η, (g x, η) ∈ T.waveFrontSet → (fderiv ℝ g x).adjoint η ≠ 0) :
    T.pullback g hg hgΩ hT =
      compCLMOfSubmersion volume volume k hk hkΩ hksurj (T.pullback f hf hfΩ h) := by
  ext ψ
  rw [compCLMOfSubmersion_apply]
  -- Pair `g^* T` with `ψ ⊗ ρₙ`, and `f^* T` with `k_♯ ψ ⊗ ρₙ`, for the same bumps `ρₙ`.
  obtain ⟨σ, G, hσ0, hσW, hG⟩ :=
    exists_seq_tensor_mollifier (mapsTo_inl_addSndDomain hg.continuousOn hgΩ) ψ
  have hW (n : ℕ) : ∀ x ∈ tsupport (fiberIntegralCLM volume volume k hk hkΩ hksurj ψ),
      ∀ y ∈ closedBall (0 : E') (σ n).rOut, toLp 2 (x, y) ∈ addSndDomain hf.continuousOn Ω' := by
    intro x hx y hy
    obtain ⟨w, hw, rfl⟩ := tsupport_fiberIntegralCLM_subset volume volume hk hkΩ hksurj ψ hx
    have hwy := hσW n w hw y hy
    simp only [mem_addSndDomain, toLp_fst, toLp_snd] at hwy ⊢
    refine ⟨hkΩ hwy.1, ?_⟩
    rw [← comp_apply (f := f), ← hgfk hwy.1]
    exact hwy.2
  refine tendsto_nhds_unique (tendsto_addSndPullback_pullback hg hgΩ hT ψ hσ0 hG)
    ((tendsto_addSndPullback_pullback hf hfΩ h _ hσ0 (G := fun n ↦ tensorBump _ (σ n) (hW n))
      fun _ ↦ tensorBump_apply _ _ _).congr fun n ↦ ?_)
  rw [addSndPullback_apply, addSndPullback_apply]
  congr 1
  -- Both fibre integrals pair a test function `u` with `∫ ψ(w) ∫ ρₙ(y) u(f (k w) + y) dy dw`.
  refine (eq_fiberIntegralCLM_iff volume volume _ _ _).2 fun u hu _ _ ↦ ?_
  -- `z ↦ ∫ ρₙ(y) u(z + y) dy` is the convolution `ρₙ ⋆ u`, as `ρₙ` is even.
  have hc : Continuous fun z ↦ ∫ y, (σ n).normed volume y * u (z + y) :=
    (((σ n).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (σ n).continuous_normed
      (hu.continuous.locallyIntegrable (μ := volume))).congr fun z ↦ by
        rw [convolution_def, ← integral_neg_eq_self]
        simp [(σ n).normed_neg, sub_eq_add_neg]
  rw [integral_fiberIntegralCLM_smul volume volume _ _ _ _ hu.continuous.continuousOn]
  simp only [smul_eq_mul, addSnd_apply, tensorBump_apply, hG]
  rw [integral_mul_addSnd_eq hf.continuousOn _ (σ n) hu.continuous,
    integral_mul_addSnd_eq hg.continuousOn ψ (σ n) hu.continuous]
  have hk_int := integral_fiberIntegralCLM_smul volume volume hk hkΩ hksurj ψ
    (hc.comp_continuousOn hf.continuousOn)
  simp only [smul_eq_mul, comp_apply] at hk_int
  rw [hk_int]
  refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
  dsimp only
  by_cases hw : w ∈ Ω₀
  · rw [hgfk hw, comp_apply]
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hw (ψ.tsupport_subset h), zero_mul, zero_mul]

/-- **Composition with a submersion.** If `k` is a submersion from `Ω₀` into `Ω` and the wave front
set of `T` does not meet the normal set of `f`, then `(f ∘ k)^* T = k^* (f^* T)`. -/
theorem pullback_comp_of_surjective (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
    (hk : ContDiffOn ℝ ∞ k Ω₀) (hkΩ : MapsTo k Ω₀ Ω)
    (hksurj : ∀ x ∈ Ω₀, Surjective (fderiv ℝ k x)) {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    T.pullback (f ∘ k) (hf.comp hk hkΩ) (hfΩ.comp hkΩ)
        (adjoint_fderiv_apply_ne_zero_comp_of_surjective (hf.differentiableOn (by simp))
          (hk.differentiableOn (by simp)) hkΩ hksurj h) =
      (T.pullback f hf hfΩ h).pullback k hk hkΩ
        (adjoint_fderiv_apply_ne_zero_of_surjective hksurj _) := by
  rw [pullback_eq_compCLMOfSubmersion hk hkΩ hksurj]
  exact pullback_eq_compCLMOfSubmersion_pullback hf hfΩ hk hkΩ hksurj _ _ (fun _ _ ↦ rfl) h _

/-- **Locality of the pullback in the source.** Restricting `f^* T` to an open set `U ≤ Ω` gives
the pullback of `T` along `f` on `U`. -/
@[simp]
theorem restrictCLM_pullback (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') {U : Opens E}
    (hU : U ≤ Ω) {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (restrictCLM (T.pullback f hf hfΩ h) : 𝓓'(U, ℂ)) =
      T.pullback f (hf.mono hU) (hfΩ.mono_left hU) fun x hx ↦ h x (hU hx) := by
  have hUΩ : MapsTo (id : E → E) U Ω := fun _ hx ↦ hU hx
  rw [pullback_eq_compCLMOfSubmersion_pullback hf hfΩ contDiffOn_id hUΩ
    (fun x _ ↦ by simpa using surjective_id) (hf.mono hU) (hfΩ.mono_left hU) (fun _ _ ↦ rfl) h,
    compCLMOfSubmersion_id]

/-- **The pullback only depends on the map on `Ω`.** -/
theorem pullback_congr (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω') {f₂ : E → E'}
    (hff₂ : EqOn f f₂ Ω) {hf₂ : ContDiffOn ℝ ∞ f₂ Ω} {hf₂Ω : MapsTo f₂ Ω Ω'} {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0)
    {h₂ : ∀ x ∈ Ω, ∀ η, (f₂ x, η) ∈ T.waveFrontSet → (fderiv ℝ f₂ x).adjoint η ≠ 0} :
    T.pullback f₂ hf₂ hf₂Ω h₂ = T.pullback f hf hfΩ h := by
  rw [pullback_eq_compCLMOfSubmersion_pullback hf hfΩ contDiffOn_id (mapsTo_id (Ω : Set E))
    (fun x _ ↦ by simpa using surjective_id) hf₂ hf₂Ω (fun _ hx ↦ (hff₂ hx).symm) h,
    compCLMOfSubmersion_id, restrictCLM_self]

/-- **Locality of the pullback in the target.** If `f` maps `Ω` into an open set `Ω'' ≤ Ω'`, the
pullback of the restriction of `T` to `Ω''` is the pullback of `T`. -/
theorem pullback_restrictCLM (hf : ContDiffOn ℝ ∞ f Ω) {Ω'' : Opens E'} (hΩ'' : Ω'' ≤ Ω')
    (hfΩ'' : MapsTo f Ω Ω'') {T : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (f x, η) ∈ T.waveFrontSet → (fderiv ℝ f x).adjoint η ≠ 0) :
    (restrictCLM T : 𝓓'(Ω'', ℂ)).pullback f hf hfΩ''
        (fun x hx η hη ↦ h x hx η ((waveFrontSet_restrictCLM hΩ'' T).subset hη).1) =
      T.pullback f hf (hfΩ''.mono_right hΩ'') h := by
  ext ψ
  -- Pair both pullbacks with `ψ ⊗ ρₙ`, a test function on the smaller and the larger domain.
  obtain ⟨σ, G, hσ0, hσW, hG⟩ :=
    exists_seq_tensor_mollifier (mapsTo_inl_addSndDomain hf.continuousOn hfΩ'') ψ
  have hW (n : ℕ) : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : E') (σ n).rOut,
      toLp 2 (x, y) ∈ addSndDomain hf.continuousOn Ω' := fun x hx y hy ↦
    have hxy := mem_addSndDomain.1 (hσW n x hx y hy)
    mem_addSndDomain.2 ⟨hxy.1, hΩ'' hxy.2⟩
  refine tendsto_nhds_unique (tendsto_addSndPullback_pullback hf hfΩ'' _ ψ hσ0 hG)
    ((tendsto_addSndPullback_pullback hf _ h ψ hσ0 (G := fun n ↦ tensorBump ψ (σ n) (hW n))
      fun _ ↦ tensorBump_apply _ _ _).congr fun n ↦ ?_)
  rw [addSndPullback_apply, addSndPullback_apply, restrictCLM_apply]
  congr 1
  refine ((eq_fiberIntegralCLM_iff volume volume _ _ _).2 fun u hu _ _ ↦ ?_).symm
  simp only [monoCLM_apply, hΩ'', le_refl, and_self, ↓reduceIte]
  rw [integral_fiberIntegralCLM_smul volume volume _ _ _ _ hu.continuous.continuousOn]
  simp only [hG, tensorBump_apply]

end Comp

end Distribution
