/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TestFunction.FiberIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

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
`Distribution.compCLMOfOpenPartialHomeomorph`. The pullback is functorial, `(g ∘ f)^* = f^* ∘ g^*`,
and local: it only depends on `f` on `Ω`, and restricting `f^* T` to an open subset `U` of `Ω` gives
the pullback of `T` along `f` on `U`. Its complex-linear extension to complex test functions pairs
`f^* T` with `φ` as `T` with the fibre integral of `φ`. Along a linear map `A`, the pullback has
vanishing derivatives along `ker A`. The tensor product commutes with pullback along a product
`k₁ × k₂` of submersions, by the identity `(k₁ × k₂)_♯ (φ ⊗ ψ) = k₁_♯ φ ⊗ k₂_♯ ψ` of fibre
integrals.

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
* `Distribution.compCLMOfSubmersion_comp`: `(g ∘ f)^* = f^* ∘ g^*`.
* `Distribution.compCLMOfSubmersion_congr`, `Distribution.restrictCLM_compCLMOfSubmersion`: the
  pullback only depends on `f` on `Ω`, and commutes with restriction to open subsets of `Ω`.
* `Distribution.compCLMOfSubmersion_id`: the pullback along the inclusion of an open subset is the
  restriction to it.
* `Distribution.complexPairing_compCLMOfSubmersion`: the pairing of `f^* T` with a complex test
  function `φ` is that of `T` with the fibre integral of `φ`.
* `Distribution.lineDerivOp_compCLMOfSubmersion_eq_zero`: the pullback along a linear map `A` has
  vanishing derivatives along `ker A`.
* `Distribution.compCLMOfSubmersion_prodMap_tensorProduct`: the tensor product commutes with
  pullback along products of submersions, `(k₁ × k₂)^* (S ⊗ T) = k₁^* S ⊗ k₂^* T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (Theorem 6.1.2).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory LineDeriv
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

/-- The pullback only depends on the values of the submersion on `Ω`. -/
theorem compCLMOfSubmersion_congr {f₂ : E → E'} (h : EqOn f f₂ Ω)
    {hf₂ : ContDiffOn ℝ ∞ f₂ Ω} {hf₂Ω : MapsTo f₂ Ω Ω'}
    {hsurj₂ : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ f₂ x)} :
    (compCLMOfSubmersion μ ν f₂ hf₂ hf₂Ω hsurj₂ : 𝓓'(Ω', F) →L[ℝ] 𝓓'(Ω, F)) =
      compCLMOfSubmersion μ ν f hf hfΩ hsurj := by
  ext T φ
  rw [compCLMOfSubmersion_apply, compCLMOfSubmersion_apply,
    fiberIntegralCLM_congr μ ν hf hfΩ hsurj h]

/-- **Restriction of the pullback**: on an open set `U ≤ Ω`, the pullback `f^* T` restricts to
the pullback of `T` along `f` on `U`. -/
@[simp]
theorem restrictCLM_compCLMOfSubmersion {U : Opens E} (hU : U ≤ Ω) (T : 𝓓'(Ω', F)) :
    restrictCLM (compCLMOfSubmersion μ ν f hf hfΩ hsurj T) =
      compCLMOfSubmersion μ ν f (hf.mono hU) (hfΩ.mono_left hU)
        (fun x hx ↦ hsurj x (hU hx)) T := by
  ext φ
  rw [restrictCLM_apply, compCLMOfSubmersion_apply, compCLMOfSubmersion_apply,
    fiberIntegralCLM_monoCLM μ ν hf hfΩ hsurj hU]

/-- **Pullback along an open inclusion.** For an open set `U` mapped into `Ω₁` by the identity,
the pullback along the identity, with one Haar measure, is the restriction to `U`. -/
@[simp]
theorem compCLMOfSubmersion_id {U Ω₁ : Opens E} {hid : ContDiffOn ℝ ∞ (id : E → E) U}
    {hidΩ : MapsTo (id : E → E) U Ω₁}
    {hidsurj : ∀ x ∈ U, Function.Surjective (fderiv ℝ (id : E → E) x)} :
    (compCLMOfSubmersion μ μ id hid hidΩ hidsurj : 𝓓'(Ω₁, F) →L[ℝ] 𝓓'(U, F)) = restrictCLM := by
  have hU : U ≤ Ω₁ := fun x hx ↦ hidΩ hx
  ext T φ
  rw [compCLMOfSubmersion_apply, restrictCLM_apply]
  congr 1
  refine ((eq_fiberIntegralCLM_iff μ μ _ _ _).2 fun g _ _ _ ↦ ?_).symm
  simp [monoCLM_apply, hU]

/-- **The pullback is functorial**: pulling back along `g` and then along `f` is pulling back
along `g ∘ f`. -/
theorem compCLMOfSubmersion_comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [FiniteDimensional ℝ E''] [MeasurableSpace E''] [BorelSpace E''] (ρ : Measure E'')
    [ρ.IsAddHaarMeasure] {Ω'' : Opens E''} {g : E' → E''} (hg : ContDiffOn ℝ ∞ g Ω')
    (hgΩ : MapsTo g Ω' Ω'') (hgsurj : ∀ y ∈ Ω', Function.Surjective (fderiv ℝ g y))
    {hgf : ContDiffOn ℝ ∞ (g ∘ f) Ω} {hgfΩ : MapsTo (g ∘ f) Ω Ω''}
    {hgfsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ (g ∘ f) x)} (T : 𝓓'(Ω'', F)) :
    compCLMOfSubmersion μ ρ (g ∘ f) hgf hgfΩ hgfsurj T =
      compCLMOfSubmersion μ ν f hf hfΩ hsurj (compCLMOfSubmersion ν ρ g hg hgΩ hgsurj T) := by
  ext φ
  rw [compCLMOfSubmersion_apply, compCLMOfSubmersion_apply, compCLMOfSubmersion_apply,
    fiberIntegralCLM_comp μ ν hf hfΩ hsurj ρ hg hgΩ hgsurj, ContinuousLinearMap.comp_apply]

end General

section Linear

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {A : E →L[ℝ] E'} (hf : ContDiffOn ℝ ∞ A Ω) (hAΩ : MapsTo A Ω Ω')
  (hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ A x))

/-- **Vanishing derivatives along the kernel.** The derivative of the pullback along a linear map
`A` in the direction of every `k ∈ ker A` vanishes. -/
theorem lineDerivOp_compCLMOfSubmersion_eq_zero (T : 𝓓'(Ω', F)) {k : E} (hk : A k = 0) :
    ∂_{k} (compCLMOfSubmersion μ ν A hf hAΩ hsurj T) = 0 := by
  -- The fibre integral of `∂_k φ` vanishes: integrate by parts against `g ∘ A`, which is constant
  -- along `k`.
  have h0 (φ : 𝓓(Ω, ℝ)) : fiberIntegralCLM μ ν A hf hAΩ hsurj (∂_{k} φ) = 0 := by
    refine ((eq_fiberIntegralCLM_iff μ ν hf hAΩ hsurj).2 fun g hg _ _ ↦ ?_).symm
    have hgA : Continuous fun x ↦ g (A x) := hg.continuous.comp A.continuous
    set φ' : 𝓓(Ω, ℝ) := ∂_{k} φ
    have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := μ)
      (B := ContinuousLinearMap.lsmul ℝ ℝ) (f := fun x ↦ g (A x)) (f' := 0) (g := (φ : E → ℝ))
      (g' := (φ' : E → ℝ)) (v := k)
      (by simp) ((hgA.smul φ'.continuous).integrable_of_hasCompactSupport
        φ'.hasCompactSupport.smul_left)
      ((hgA.smul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_left)
      (fun x _ ↦ ?_) (fun x _ ↦ ?_)
    · simp only [ContinuousLinearMap.lsmul_apply, Pi.zero_apply, zero_smul, integral_zero,
        neg_zero] at hibp
      simp only [FunLike.coe_zero, Pi.zero_apply, zero_smul, integral_zero]
      rw [← hibp]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by simp [smul_eq_mul, mul_comm])
    · -- `g ∘ A` is constant along `k`.
      have hc : (fun t : ℝ ↦ g (A (x + t • k))) = fun _ ↦ g (A x) := by
        ext t
        simp [hk]
      rw [HasLineDerivAt, hc]
      exact hasDerivAt_const _ _
    · have hφx : (∂_{k} φ : 𝓓(Ω, ℝ)) x = lineDeriv ℝ φ x k :=
        lineDerivCLM_apply_of_le (by simp)
      rw [hφx]
      exact (φ.contDiff.differentiable (by simp) x).lineDifferentiableAt.hasLineDerivAt
  ext φ
  simp [lineDerivOp_apply_apply, compCLMOfSubmersion_apply, h0]

end Linear

/-- **The pullback on complex test functions.** If the complex test function `ψ` on `Ω'`
integrates against every smooth real function `g` compactly supported in `Ω'` as the complex test
function `φ` on `Ω` against `g ∘ f`, that is, `ψ` is the fibre integral of `φ`, then `f^* T` pairs
with `φ` as `T` pairs with `ψ`. -/
theorem complexPairing_compCLMOfSubmersion (T : 𝓓'(Ω', ℂ)) {φ : 𝓓(Ω, ℂ)} {ψ : 𝓓(Ω', ℂ)}
    (h : ∀ g : E' → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ω' →
      ∫ y, ψ y * g y ∂ν = ∫ x, φ x * g (f x) ∂μ) :
    (compCLMOfSubmersion μ ν f hf hfΩ hsurj T).complexPairing φ = T.complexPairing ψ := by
  -- The real and imaginary parts of `ψ` are the fibre integrals of those of `φ`.
  have hpart (L : ℂ →L[ℝ] ℝ) : postcompCLM (𝕜 := ℝ) L ψ =
      fiberIntegralCLM μ ν f hf hfΩ hsurj (postcompCLM (𝕜 := ℝ) L φ) := by
    refine (eq_fiberIntegralCLM_iff μ ν hf hfΩ hsurj).2 fun g hg hgc hgΩ ↦ ?_
    have hψ : Integrable (fun y ↦ ψ y * g y) ν :=
      (ψ.continuous.mul (Complex.continuous_ofReal.comp
        hg.continuous)).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right
    -- `x ↦ φ x * g (f x)` is continuous on the compact support of `φ` and vanishes off it.
    have hφ : Integrable (fun x ↦ φ x * g (f x)) μ := by
      refine (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_left _ _).trans (subset_tsupport _))).1
        (ContinuousOn.integrableOn_compact φ.hasCompactSupport.isCompact ?_)
      exact φ.continuous.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
        (hg.continuous.comp_continuousOn (hf.continuousOn.mono φ.tsupport_subset)))
    have hL (z : ℂ) (t : ℝ) : L z • t = L (z * t) := by
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, Complex.real_smul, mul_comm]
    simp only [postcompCLM_apply, Function.comp_apply, hL]
    rw [L.integral_comp_comm hψ, L.integral_comp_comm hφ, h g hg hgc hgΩ]
  simp only [complexPairing_apply, compCLMOfSubmersion_apply, hpart]

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

/-! ### Tensor products -/

section Prod

variable {E₀ D₀ D : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [MeasurableSpace E₀] [BorelSpace E₀] [NormedAddCommGroup D₀] [NormedSpace ℝ D₀]
  [FiniteDimensional ℝ D₀] [MeasurableSpace D₀] [BorelSpace D₀] [NormedAddCommGroup D]
  [NormedSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  {Ω₀ : Opens E₀} {O₀ : Opens D₀} {O : Opens D}
  {V₀ : Opens (E₀ × D₀)} {V : Opens (E × D)} {k₁ : E₀ → E} {k₂ : D₀ → D}

/-- **The tensor product commutes with pullback along submersions**:
`(k₁ × k₂)^* (S ⊗ T) = k₁^* S ⊗ k₂^* T`, the pullbacks being taken by integration over the fibres,
with the product measures on the products. -/
theorem compCLMOfSubmersion_prodMap_tensorProduct
    (μ₁ : Measure E₀) [μ₁.IsAddHaarMeasure] (μ₂ : Measure D₀) [μ₂.IsAddHaarMeasure]
    (ν₁ : Measure E) [ν₁.IsAddHaarMeasure] (ν₂ : Measure D) [ν₂.IsAddHaarMeasure]
    (hk₁ : ContDiffOn ℝ ∞ k₁ Ω₀) (hk₁Ω : MapsTo k₁ Ω₀ Ω)
    (hk₁s : ∀ x ∈ Ω₀, Function.Surjective (fderiv ℝ k₁ x))
    (hk₂ : ContDiffOn ℝ ∞ k₂ O₀) (hk₂O : MapsTo k₂ O₀ O)
    (hk₂s : ∀ x ∈ O₀, Function.Surjective (fderiv ℝ k₂ x))
    (hV₀ : (V₀ : Set (E₀ × D₀)) = (Ω₀ : Set E₀) ×ˢ (O₀ : Set D₀))
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    {hk : ContDiffOn ℝ ∞ (Prod.map k₁ k₂) V₀} {hkV : MapsTo (Prod.map k₁ k₂) V₀ V}
    {hks : ∀ p ∈ V₀, Function.Surjective (fderiv ℝ (Prod.map k₁ k₂) p)}
    (S : 𝓓'(Ω, ℂ)) (T : 𝓓'(O, ℂ)) :
    compCLMOfSubmersion (μ₁.prod μ₂) (ν₁.prod ν₂) (Prod.map k₁ k₂) hk hkV hks
        (S.tensorProduct T hV.subset) =
      (compCLMOfSubmersion μ₁ ν₁ k₁ hk₁ hk₁Ω hk₁s S).tensorProduct
        (compCLMOfSubmersion μ₂ ν₂ k₂ hk₂ hk₂O hk₂s T) hV₀.subset := by
  refine (tensorProduct_eq _ _ hV₀ fun φ ψ ↦ ?_).symm
  rw [compCLMOfSubmersion_apply, compCLMOfSubmersion_apply, compCLMOfSubmersion_apply,
    fiberIntegralCLM_prodMap_prodSMulCLM μ₁ μ₂ ν₁ ν₂ hk₁ hk₁Ω hk₁s hk₂ hk₂O hk₂s hV₀ hV,
    tensorProduct_prodSMulCLM]

end Prod

end Distribution
