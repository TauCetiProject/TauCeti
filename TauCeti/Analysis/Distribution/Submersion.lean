/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TestFunction.FiberIntegral

/-!
# Pullback of distributions along submersions

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of finite-dimensional real normed spaces with additive
Haar measures `μ` and `ν`, and let `f : E → E'` be smooth on `Ω`, map `Ω` into `Ω'`, and have
surjective derivative at every point of `Ω`. Every distribution `T` on `Ω'` pulls back along `f` to
the distribution on `Ω`

`(f^* T) φ = T (f_♯ φ)`,

where `f_♯ φ` is the integral of the test density `φ` over the fibres of `f`
(`TestFunction.fiberIntegralCLM`). No condition on the wave front set of `T` is needed: the normal
set `{(f x, η) | η ≠ 0, (Df x)ᵀ η = 0}` of a submersion is empty. On the distribution of a function
`g` continuous on `Ω'`, the pullback is the distribution of `g ∘ f`
(`Distribution.compCLMOfSubmersion_ofFun`); on `Ω`, the support of `f^* T` lies in the preimage
of the support of `T`; and when `f` is a change of variables and `μ = ν`, `f^*` is the pullback
`Distribution.compCLMOfOpenPartialHomeomorph`.

Typical submersions are the projections of a product, coordinate charts followed by projections,
and the maps `(x, y) ↦ x - y`, along which a distribution in one variable becomes a distribution
constant along parallel hyperplanes.

## Main declarations

* `Distribution.compCLMOfSubmersion`: the pullback `T ↦ f^* T`, as a continuous linear map
  `𝓓'(Ω', F) →L[ℝ] 𝓓'(Ω, F)`.
* `Distribution.compCLMOfSubmersion_ofFun`: `f^*` sends the distribution of a function continuous
  on `Ω'` to that of its composition with `f`.
* `Distribution.dsupport_compCLMOfSubmersion_inter_subset`: on `Ω`, the support of `f^* T` lies in
  `f⁻¹ (supp T)`.
* `Distribution.compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph`: along a change of
  variables, `f^*` is the pullback by that change of variables.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (Theorem 6.1.2).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions ContDiff

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]
  {Ω : Opens E} {Ω' : Opens E'} {f : E → E'} (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
  (hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ f x))

section General

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

variable (f) in
/-- The **pullback of a distribution along a submersion** `f`, smooth on `Ω` with surjective
derivative at every point of `Ω` and mapping `Ω` into `Ω'`: a distribution `T` on `Ω'` pulls back to
the distribution `φ ↦ T (f_♯ φ)` on `Ω`, where `f_♯ φ` is the integral of the test density `φ` over
the fibres of `f`, computed with the Haar measures `μ` and `ν` (`TestFunction.fiberIntegralCLM`).
On a function `g` continuous on `Ω'` it gives `g ∘ f` (`Distribution.compCLMOfSubmersion_ofFun`). -/
def compCLMOfSubmersion : 𝓓'(Ω', F) →L[ℝ] 𝓓'(Ω, F) :=
  (fiberIntegralCLM μ ν f hf hfΩ hsurj).precompCompactConvergenceCLM F

/-- The pullback `f^* T` pairs a test function `φ` with `T` through `T (f_♯ φ)`. -/
@[simp]
theorem compCLMOfSubmersion_apply (T : 𝓓'(Ω', F)) (φ : 𝓓(Ω, ℝ)) :
    compCLMOfSubmersion μ ν f hf hfΩ hsurj T φ = T (fiberIntegralCLM μ ν f hf hfΩ hsurj φ) :=
  (rfl)

/-- On `Ω`, the support of the pullback `f^* T` lies in the preimage of the support of `T`. -/
theorem dsupport_compCLMOfSubmersion_inter_subset (T : 𝓓'(Ω', F)) :
    dsupport (compCLMOfSubmersion μ ν f hf hfΩ hsurj T) ∩ Ω ⊆ f ⁻¹' dsupport T := by
  rintro x ⟨hx, hxΩ⟩
  by_contra hxT
  obtain ⟨s, hT, hs, hxs⟩ := (notMem_dsupport_iff _).1 hxT
  -- `T` vanishes on `s`, so `f^* T` vanishes on `Ω ∩ f ⁻¹' s`, since `f_♯` maps test functions
  -- supported there to test functions supported in `s`.
  refine (notMem_dsupport_iff (f := compCLMOfSubmersion μ ν f hf hfΩ hsurj T) x).2
    ⟨Ω ∩ f ⁻¹' s, fun φ hφ ↦ ?_, hf.continuousOn.isOpen_inter_preimage Ω.isOpen hs, hxΩ, hxs⟩ hx
  rw [compCLMOfSubmersion_apply]
  refine hT _ ((tsupport_fiberIntegralCLM_subset μ ν hf hfΩ hsurj φ).trans ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact (hφ hy).2

/-- Along a change of variables `e`, the pullback with respect to one Haar measure is
`Distribution.compCLMOfOpenPartialHomeomorph`. -/
theorem compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {Ω₁ Ω₂ : Opens E} (hΩ₁ : (Ω₁ : Set E) ⊆ e.source) (hΩ₁₂ : MapsTo e Ω₁ Ω₂)
    {hsurj : ∀ x ∈ Ω₁, Function.Surjective (fderiv ℝ e x)} :
    (compCLMOfSubmersion μ μ e (he.mono hΩ₁) hΩ₁₂ hsurj : 𝓓'(Ω₂, F) →L[ℝ] 𝓓'(Ω₁, F)) =
      compCLMOfOpenPartialHomeomorph e he he' hΩ₁ hΩ₁₂ := by
  ext T φ
  rw [compCLMOfSubmersion_apply, compCLMOfOpenPartialHomeomorph_apply,
    fiberIntegralCLM_eq_pushforwardCLM]

end General

/-- On the distribution of a function `g` continuous on `Ω'`, the pullback along `f` is the
distribution of `g ∘ f`. -/
theorem compCLMOfSubmersion_ofFun {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {g : E' → F} (hg : ContinuousOn g Ω') :
    compCLMOfSubmersion μ ν f hf hfΩ hsurj (ofFun Ω' g ν ⊤) =
      ofFun Ω (fun x ↦ g (f x)) μ ⊤ := by
  have hgf : ContinuousOn (fun x ↦ g (f x)) Ω := hg.comp hf.continuousOn hfΩ
  ext φ
  rw [compCLMOfSubmersion_apply, ofFun_apply (hg.locallyIntegrableOn Ω'.isOpen.measurableSet),
    ofFun_apply (hgf.locallyIntegrableOn Ω.isOpen.measurableSet),
    integral_fiberIntegralCLM_smul μ ν hf hfΩ hsurj φ hg]

end Distribution
