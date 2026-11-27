/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Comp
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Product
public import TauCeti.Analysis.Distribution.WaveFrontSet.Submersion
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Tensor products and products of distributions under pullback along submersions

Let `k` be a submersion from an open set `Ω₀` of a finite-dimensional real inner product space
`E₀` into an open set `Ω` of `E`: smooth, with surjective derivative at every point of `Ω₀`. Every
distribution `T` on `Ω` has a pullback `k^* T` to `Ω₀`, by integration over the fibres of `k`
(`Distribution.compCLMOfSubmersion`). On functions it is composition with `k`, so it should be
multiplicative. This file proves that it is, for the product of distributions under Hörmander's
wave front condition (`Distribution.product`):

`k^* (S T) = (k^* S) (k^* T)`

(`Distribution.compCLMOfSubmersion_product`). The wave front condition passes to the pullbacks
(`Distribution.NoOppositeCovectorsOn.compCLMOfSubmersion`): covectors of `WF(k^* S)` over `x` are
the images `Dk(x)ᵀ η` of covectors `η` of `WF(S)` over `k x`
(`Distribution.waveFrontSet_compCLMOfSubmersion`), and `Dk(x)ᵀ` is injective, so opposite
covectors of `WF(k^* S)` and `WF(k^* T)` come from opposite covectors of `WF(S)` and `WF(T)`.

A smooth change of variables is a submersion, so the product of distributions does not depend on
the coordinates (`Distribution.compCLMOfOpenPartialHomeomorph_product`). This is what lets the
product of distributions be read in the charts of a manifold.

## The argument

The product is the pullback of the tensor product along the diagonal
(`Distribution.pullback_diagonal_transportCLM_tensorProduct_eq_product`), and pullbacks compose
with submersions on either side (`Distribution.pullback_comp_of_surjective`,
`Distribution.pullback_eq_pullback_compCLMOfSubmersion`). Since `Δ ∘ k = (k × k) ∘ Δ₀` for the
diagonals `Δ` and `Δ₀`,

`k^* (S T) = k^* Δ^* (S ⊗ T) = Δ₀^* (k × k)^* (S ⊗ T)`.

It remains to see that the tensor product commutes with pullback along products of submersions,

`(k₁ × k₂)^* (S ⊗ T) = k₁^* S ⊗ k₂^* T`

(`Distribution.compCLMOfSubmersion_prodMap_tensorProduct`). By uniqueness of the tensor product
(`Distribution.tensorProduct_eq`), it suffices to evaluate both sides on tensor products of test
functions, so this is the identity `(k₁ × k₂)_♯ (φ ⊗ ψ) = k₁_♯ φ ⊗ k₂_♯ ψ` of fibre integrals
(`TestFunction.fiberIntegralCLM_prodMap_prodSMulCLM`), which follows from Fubini's theorem and the
defining identity of fibre integration.

## Main results

* `TestFunction.fiberIntegralCLM_prodMap_prodSMulCLM`: the fibre integral of `φ ⊗ ψ` along
  `k₁ × k₂` is `k₁_♯ φ ⊗ k₂_♯ ψ`.
* `Distribution.compCLMOfSubmersion_prodMap_tensorProduct`:
  `(k₁ × k₂)^* (S ⊗ T) = k₁^* S ⊗ k₂^* T`.
* `Distribution.NoOppositeCovectorsOn.compCLMOfSubmersion`: the wave front condition for the
  product passes to pullbacks along submersions.
* `Distribution.compCLMOfSubmersion_product`: `k^* (S T) = (k^* S) (k^* T)`.
* `Distribution.compCLMOfOpenPartialHomeomorph_product`: the same for a smooth change of
  variables `e`, `e^* (S T) = (e^* S) (e^* T)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorems 8.2.4 and 8.2.10.
-/

public section

noncomputable section

open Function MeasureTheory Set TopologicalSpace TestFunction WithLp TauCeti
open scoped Distributions ContDiff

/-! ### Fibre integrals along products of submersions -/

section Prod

variable {E₀ D₀ E D : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup D₀]
  [NormedSpace ℝ D₀] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {Ω₀ : Opens E₀} {O₀ : Opens D₀} {Ω : Opens E} {O : Opens D}
  {V₀ : Opens (E₀ × D₀)} {V : Opens (E × D)} {k₁ : E₀ → E} {k₂ : D₀ → D}
  (hk₁ : ContDiffOn ℝ ∞ k₁ Ω₀) (hk₁Ω : MapsTo k₁ Ω₀ Ω)
  (hk₁s : ∀ x ∈ Ω₀, Surjective (fderiv ℝ k₁ x))
  (hk₂ : ContDiffOn ℝ ∞ k₂ O₀) (hk₂O : MapsTo k₂ O₀ O)
  (hk₂s : ∀ x ∈ O₀, Surjective (fderiv ℝ k₂ x))

include hk₁ hk₂ hk₁s hk₂s in
/-- The derivative of a product `k₁ × k₂` of submersions is surjective on the product of their
domains. -/
theorem TauCeti.surjective_fderiv_prodMap {p : E₀ × D₀} (hp : p ∈ (Ω₀ : Set E₀) ×ˢ (O₀ : Set D₀)) :
    Surjective (fderiv ℝ (Prod.map k₁ k₂) p) := by
  have h₁ : HasFDerivAt k₁ (fderiv ℝ k₁ p.1) p.1 :=
    ((hk₁.differentiableOn (by simp) _ hp.1).differentiableAt
      (Ω₀.isOpen.mem_nhds hp.1)).hasFDerivAt
  have h₂ : HasFDerivAt k₂ (fderiv ℝ k₂ p.2) p.2 :=
    ((hk₂.differentiableOn (by simp) _ hp.2).differentiableAt
      (O₀.isOpen.mem_nhds hp.2)).hasFDerivAt
  rw [(h₁.prodMap p h₂).fderiv, ContinuousLinearMap.coe_prodMap']
  exact (hk₁s _ hp.1).prodMap (hk₂s _ hp.2)

variable [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ D₀]
  [MeasurableSpace D₀] [BorelSpace D₀] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  (μ₁ : Measure E₀) [μ₁.IsAddHaarMeasure] (μ₂ : Measure D₀) [μ₂.IsAddHaarMeasure]
  (ν₁ : Measure E) [ν₁.IsAddHaarMeasure] (ν₂ : Measure D) [ν₂.IsAddHaarMeasure]
  (hV₀ : (V₀ : Set (E₀ × D₀)) = (Ω₀ : Set E₀) ×ˢ (O₀ : Set D₀))
  (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))

/-- **Fibre integrals of tensor products.** Integrating `(x, y) ↦ φ x ψ y` over the fibres of
`k₁ × k₂`, with the product measures, gives `(x', y') ↦ (k₁_♯ φ) x' (k₂_♯ ψ) y'`. -/
theorem TestFunction.fiberIntegralCLM_prodMap_prodSMulCLM (φ : 𝓓(Ω₀, ℝ)) (ψ : 𝓓(O₀, ℝ)) :
    fiberIntegralCLM (μ₁.prod μ₂) (ν₁.prod ν₂) (Prod.map k₁ k₂)
        (hV₀ ▸ hk₁.prodMap hk₂) (hV₀ ▸ hV ▸ hk₁Ω.prodMap hk₂O)
        (fun p hp ↦ surjective_fderiv_prodMap hk₁ hk₁s hk₂ hk₂s (hV₀ ▸ hp))
        (prodSMulCLM ψ hV₀.symm.subset φ) =
      prodSMulCLM (fiberIntegralCLM μ₂ ν₂ k₂ hk₂ hk₂O hk₂s ψ) hV.symm.subset
        (fiberIntegralCLM μ₁ ν₁ k₁ hk₁ hk₁Ω hk₁s φ) := by
  set φ' := fiberIntegralCLM μ₁ ν₁ k₁ hk₁ hk₁Ω hk₁s φ
  set ψ' := fiberIntegralCLM μ₂ ν₂ k₂ hk₂ hk₂O hk₂s ψ
  set Θ := prodSMulCLM ψ' hV.symm.subset φ'
  set Θ₀ := prodSMulCLM ψ hV₀.symm.subset φ
  symm
  refine (eq_fiberIntegralCLM_iff _ _ _ _ _).2 fun g hg hgc _ ↦ ?_
  -- The partial integral `h y₁ = ∫ ψ'(y₂) g(y₁, y₂) dy₂` is continuous in `y₁`.
  set h : E → ℝ := fun y₁ ↦ ∫ y₂, ψ' y₂ * g (y₁, y₂) ∂ν₂ with h_def
  have hh : Continuous h :=
    continuous_integral_of_hasCompactSupport_uncurry (f := fun y₁ y₂ ↦ ψ' y₂ * g (y₁, y₂))
      ((ψ'.continuous.comp continuous_snd).mul hg.continuous) hgc.mul_left
  -- Both sides are iterated integrals; the inner integrals are computed by fibre integration.
  have hint₁ : Integrable (fun q ↦ Θ q • g q) (ν₁.prod ν₂) :=
    (Θ.continuous.smul hg.continuous).integrable_of_hasCompactSupport
      Θ.hasCompactSupport.smul_right
  have hint₂ : Integrable (fun q ↦ Θ₀ q • g (Prod.map k₁ k₂ q)) (μ₁.prod μ₂) := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_of_tsupport fun q hq ↦ ?_)
      Θ₀.hasCompactSupport.smul_right
    have hq' : q ∈ (Ω₀ : Set E₀) ×ˢ (O₀ : Set D₀) :=
      hV₀ ▸ Θ₀.tsupport_subset (tsupport_smul_subset_left _ _ hq)
    have hKq : ContinuousAt (Prod.map k₁ k₂) q :=
      ((hk₁.continuousOn.prodMap hk₂.continuousOn) q hq').continuousAt
        ((Ω₀.isOpen.prod O₀.isOpen).mem_nhds hq')
    exact Θ₀.continuous.continuousAt.smul (hg.continuous.continuousAt.comp hKq)
  rw [integral_prod _ hint₁, integral_prod _ hint₂]
  simp only [Θ, Θ₀, prodSMulCLM_apply, smul_eq_mul, Prod.map_apply]
  have hin (x₁ : E₀) :
      ∫ x₂, ψ x₂ * φ x₁ * g (k₁ x₁, k₂ x₂) ∂μ₂ = φ x₁ * h (k₁ x₁) := by
    have := integral_fiberIntegralCLM_smul μ₂ ν₂ hk₂ hk₂O hk₂s ψ
      (g := fun y₂ ↦ g (k₁ x₁, y₂))
      (hg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    simp only [smul_eq_mul] at this
    rw [h_def]
    dsimp only
    rw [this, ← integral_const_mul]
    congr 1
    funext x₂
    ring
  have hout : ∫ y₁, φ' y₁ * h y₁ ∂ν₁ = ∫ x₁, φ x₁ * h (k₁ x₁) ∂μ₁ := by
    simpa only [smul_eq_mul] using
      integral_fiberIntegralCLM_smul μ₁ ν₁ hk₁ hk₁Ω hk₁s φ hh.continuousOn
  simp only [hin]
  rw [← hout]
  congr 1
  funext y₁
  rw [h_def]
  dsimp only
  rw [← integral_const_mul]
  congr 1
  funext y₂
  ring

namespace Distribution

variable (S : 𝓓'(Ω, ℂ)) (T : 𝓓'(O, ℂ))

/-- **The tensor product commutes with pullback along submersions**:
`(k₁ × k₂)^* (S ⊗ T) = k₁^* S ⊗ k₂^* T`, the pullbacks being taken by integration over the fibres,
with the product measures on the products. -/
theorem compCLMOfSubmersion_prodMap_tensorProduct :
    compCLMOfSubmersion (μ₁.prod μ₂) (ν₁.prod ν₂) (Prod.map k₁ k₂)
        (hV₀ ▸ hk₁.prodMap hk₂) (hV₀ ▸ hV ▸ hk₁Ω.prodMap hk₂O)
        (fun p hp ↦ surjective_fderiv_prodMap hk₁ hk₁s hk₂ hk₂s (hV₀ ▸ hp))
        (S.tensorProduct T hV.subset) =
      (compCLMOfSubmersion μ₁ ν₁ k₁ hk₁ hk₁Ω hk₁s S).tensorProduct
        (compCLMOfSubmersion μ₂ ν₂ k₂ hk₂ hk₂O hk₂s T) hV₀.subset := by
  refine (tensorProduct_eq _ _ hV₀ fun φ ψ ↦ ?_).symm
  rw [compCLMOfSubmersion_apply, compCLMOfSubmersion_apply, compCLMOfSubmersion_apply,
    fiberIntegralCLM_prodMap_prodSMulCLM hk₁ hk₁Ω hk₁s hk₂ hk₂O hk₂s μ₁ μ₂ ν₁ ν₂ hV₀ hV,
    tensorProduct_prodSMulCLM]

end Distribution

end Prod

namespace Distribution

/-! ### The product under submersions -/

variable {E₀ E : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [MeasurableSpace E₀] [BorelSpace E₀] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω₀ : Opens E₀} {Ω : Opens E} {k : E₀ → E}
  (hk : ContDiffOn ℝ ∞ k Ω₀) (hkΩ : MapsTo k Ω₀ Ω) (hks : ∀ x ∈ Ω₀, Surjective (fderiv ℝ k x))
  {S T : 𝓓'(Ω, ℂ)}

include hk hks in
/-- **The wave front condition under pullback along a submersion.** If `S` and `T` have no
opposite covectors over `k x`, then their pullbacks along the submersion `k` have none over `x`: a
covector of `WF(k^* S)` over `x` is `Dk(x)ᵀ η` for a covector `η` of `WF(S)` over `k x`, and
`Dk(x)ᵀ` is injective. -/
theorem NoOppositeCovectorsOn.compCLMOfSubmersion {μ : Measure E₀} [μ.IsAddHaarMeasure]
    {ν : Measure E} [ν.IsAddHaarMeasure] {x : E₀} (h : NoOppositeCovectorsOn S T {k x}) :
    NoOppositeCovectorsOn (compCLMOfSubmersion μ ν k hk hkΩ hks S)
      (compCLMOfSubmersion μ ν k hk hkΩ hks T) {x} := by
  rw [noOppositeCovectorsOn_singleton_iff] at h ⊢
  intro ξ hS hT
  rw [waveFrontSet_compCLMOfSubmersion] at hS hT
  obtain ⟨hxΩ, η₁, hη₁, hξ₁⟩ := hS
  obtain ⟨-, η₂, hη₂, hξ₂⟩ := hT
  dsimp only at hxΩ hη₁ hξ₁ hη₂ hξ₂
  have hinj : Injective (fderiv ℝ k x).adjoint :=
    ContinuousLinearMap.adjoint_injective_iff_denseRange.2 (hks x hxΩ).denseRange
  have : η₂ = -η₁ := hinj (by rw [hξ₂, map_neg, hξ₁])
  exact h η₁ hη₁ (this ▸ hη₂)

/-- The product `k × k` of a submersion with itself, on the Euclidean products `WithLp 2 (E₀ × E₀)`
and `WithLp 2 (E × E)`. -/
private abbrev prodMapL2 (k : E₀ → E) : WithLp 2 (E₀ × E₀) → WithLp 2 (E × E) :=
  (prodContinuousLinearEquiv 2 ℝ E E).symm ∘ Prod.map k k ∘ prodContinuousLinearEquiv 2 ℝ E₀ E₀

variable {W₀ : Opens (WithLp 2 (E₀ × E₀))} {W : Opens (WithLp 2 (E × E))}
  (hW₀ : ∀ q ∈ W₀, prodContinuousLinearEquiv 2 ℝ E₀ E₀ q ∈ (Ω₀ : Set E₀) ×ˢ (Ω₀ : Set E₀))

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include hk hW₀ in
private theorem contDiffOn_prodMapL2 : ContDiffOn ℝ ∞ (prodMapL2 k) W₀ :=
  (prodContinuousLinearEquiv 2 ℝ E E).symm.contDiff.comp_contDiffOn
    ((hk.prodMap hk).comp (prodContinuousLinearEquiv 2 ℝ E₀ E₀).contDiff.contDiffOn hW₀)

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include hk hks hW₀ in
private theorem surjective_fderiv_prodMapL2 :
    ∀ q ∈ W₀, Surjective (fderiv ℝ (prodMapL2 k) q) := by
  intro q hq
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (ContinuousLinearEquiv.surjective _).comp
    ((surjective_fderiv_prodMap hk hks hk hks (hW₀ q hq)).comp (ContinuousLinearEquiv.surjective _))

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include hkΩ hW₀ in
private theorem mapsTo_prodMapL2
    (hW : ∀ q, prodContinuousLinearEquiv 2 ℝ E E q ∈ (Ω : Set E) ×ˢ (Ω : Set E) → q ∈ W) :
    MapsTo (prodMapL2 k) W₀ W := fun q hq ↦
  hW _ (by simpa using (hkΩ.prodMap hkΩ) (hW₀ q hq))

/-- The open set `Ω ×ˢ Ω` of `E × E`. -/
private abbrev prodOpens (Ω : Opens E) : Opens (E × E) :=
  ⟨(Ω : Set E) ×ˢ (Ω : Set E), Ω.isOpen.prod Ω.isOpen⟩

/-- The open set `Ω ×ˢ Ω`, read in the Euclidean product `WithLp 2 (E × E)`. -/
private abbrev prodL2Opens (Ω : Opens E) : Opens (WithLp 2 (E × E)) :=
  ⟨prodContinuousLinearEquiv 2 ℝ E E ⁻¹' ((Ω : Set E) ×ˢ (Ω : Set E)),
    (Ω.isOpen.prod Ω.isOpen).preimage (prodContinuousLinearEquiv 2 ℝ E E).continuous⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem mapsTo_prodL2Opens (Ω : Opens E) :
    MapsTo (prodContinuousLinearEquiv 2 ℝ E E) (prodL2Opens Ω) (prodOpens Ω) :=
  fun _ hq ↦ hq

/-- The pullback of `S ⊗ T`, moved to `WithLp 2 (E × E)`, along `k × k` is `k^* S ⊗ k^* T`, moved
to `WithLp 2 (E₀ × E₀)`. -/
private theorem compCLMOfSubmersion_prodMapL2_transportCLM_tensorProduct (S T : 𝓓'(Ω, ℂ)) :
    compCLMOfSubmersion volume volume (prodMapL2 k)
        (contDiffOn_prodMapL2 hk (W₀ := prodL2Opens Ω₀) fun _ hq ↦ hq)
        (mapsTo_prodMapL2 hkΩ (fun _ hq ↦ hq) fun _ hq ↦ hq)
        (surjective_fderiv_prodMapL2 hk hks fun _ hq ↦ hq)
        (transportCLM (prodContinuousLinearEquiv 2 ℝ E E) (mapsTo_prodL2Opens Ω)
          (S.tensorProduct T (V := prodOpens Ω) subset_rfl)) =
      transportCLM (prodContinuousLinearEquiv 2 ℝ E₀ E₀) (mapsTo_prodL2Opens Ω₀)
        ((compCLMOfSubmersion volume volume k hk hkΩ hks S).tensorProduct
          (compCLMOfSubmersion volume volume k hk hkΩ hks T) (V := prodOpens Ω₀) subset_rfl) := by
  have hL : MeasurePreserving (prodContinuousLinearEquiv 2 ℝ E E) volume (volume.prod volume) :=
    WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E E
  have hL₀ : MeasurePreserving (prodContinuousLinearEquiv 2 ℝ E₀ E₀) volume (volume.prod volume) :=
    WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E₀ E₀
  ext φ
  rw [compCLMOfSubmersion_apply, transportCLM_apply, transportCLM_apply,
    ← compCLMOfSubmersion_prodMap_tensorProduct hk hkΩ hks hk hkΩ hks volume volume volume volume
      (V₀ := prodOpens Ω₀) rfl (V := prodOpens Ω) rfl S T, compCLMOfSubmersion_apply]
  congr 1
  refine (eq_fiberIntegralCLM_iff _ _ _ _ _).2 fun g hg _ _ ↦ ?_
  simp only [ContinuousLinearEquiv.transportTestFunction_apply]
  rw [← hL.integral_comp (prodContinuousLinearEquiv 2 ℝ E E).toHomeomorph.measurableEmbedding,
    ← hL₀.integral_comp
      (prodContinuousLinearEquiv 2 ℝ E₀ E₀).toHomeomorph.measurableEmbedding]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  refine (integral_fiberIntegralCLM_smul volume volume _ _ _ φ
    (g := fun y ↦ g (prodContinuousLinearEquiv 2 ℝ E E y))
    (hg.continuous.comp (prodContinuousLinearEquiv 2 ℝ E E).continuous).continuousOn).trans ?_
  simp [prodMapL2]

/-- **The product of distributions commutes with pullback along submersions**: if at every point
no covector of the wave front set of `S` is opposite to a covector of the wave front set of `T`,
then the same holds for their pullbacks along a submersion `k`
(`Distribution.NoOppositeCovectorsOn.compCLMOfSubmersion`), and

`k^* (S T) = (k^* S) (k^* T)`. -/
theorem compCLMOfSubmersion_product (h : ∀ y, NoOppositeCovectorsOn S T {y}) :
    compCLMOfSubmersion volume volume k hk hkΩ hks (S.product T h) =
      (compCLMOfSubmersion volume volume k hk hkΩ hks S).product
        (compCLMOfSubmersion volume volume k hk hkΩ hks T)
        (fun x ↦ (h (k x)).compCLMOfSubmersion hk hkΩ hks) := by
  symm
  have hΔ : MapsTo (fun x : E ↦ toLp 2 (x, x)) Ω (prodL2Opens Ω) := fun x hx ↦ ⟨hx, hx⟩
  have hΔ₀ : MapsTo (fun x : E₀ ↦ toLp 2 (x, x)) Ω₀ (prodL2Opens Ω₀) := fun x hx ↦ ⟨hx, hx⟩
  -- `k^* (S T) = k^* Δ^* (S ⊗ T) = (Δ ∘ k)^* (S ⊗ T) = Δ₀^* (k × k)^* (S ⊗ T)`, since
  -- `Δ ∘ k = (k × k) ∘ Δ₀`; then `(k × k)^* (S ⊗ T) = k^* S ⊗ k^* T` and `Δ₀^*` gives the product.
  conv_rhs => rw [← pullback_diagonal_transportCLM_tensorProduct_eq_product (V := prodOpens Ω) rfl
      (mapsTo_prodL2Opens Ω) h hΔ, ← pullback_eq_compCLMOfSubmersion hk hkΩ hks,
    ← pullback_comp_of_surjective (contDiff_toLp_diag ℝ E).contDiffOn hΔ hk hkΩ hks,
    pullback_eq_pullback_compCLMOfSubmersion (contDiff_toLp_diag ℝ E₀).contDiffOn hΔ₀
      (contDiffOn_prodMapL2 hk fun _ hq ↦ hq) (mapsTo_prodMapL2 hkΩ (fun _ hq ↦ hq) fun _ hq ↦ hq)
      (surjective_fderiv_prodMapL2 hk hks fun _ hq ↦ hq) (g := (fun x : E ↦ toLp 2 (x, x)) ∘ k) _ _
      (fun _ _ ↦ rfl)]
  rw [← pullback_diagonal_transportCLM_tensorProduct_eq_product (V := prodOpens Ω₀) rfl
    (mapsTo_prodL2Opens Ω₀) _ hΔ₀]
  congr 1
  exact (compCLMOfSubmersion_prodMapL2_transportCLM_tensorProduct hk hkΩ hks S T).symm

/-! ### Changes of variables -/

section ChangeOfVariables

variable {e : OpenPartialHomeomorph E E} (he : ContDiffOn ℝ ∞ e e.source)
  (he' : ContDiffOn ℝ ∞ e.symm e.target) {U : Opens E} (hU : (U : Set E) ⊆ e.source)
  (hUΩ : MapsTo e U Ω)

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
include he he' hU in
/-- A smooth change of variables is a submersion. -/
private theorem surjective_fderiv_of_openPartialHomeomorph :
    ∀ x ∈ U, Surjective (fderiv ℝ e x) := fun x hx ↦
  (e.isInvertible_fderiv_of_contDiffOn he he' (by simp) (hU hx)).surjective

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] in
/-- **The wave front condition under a change of variables.** If `S` and `T` have no opposite
covectors over `e x`, then `e^* S` and `e^* T` have none over `x`. -/
theorem NoOppositeCovectorsOn.compCLMOfOpenPartialHomeomorph {x : E}
    (h : NoOppositeCovectorsOn S T {e x}) :
    NoOppositeCovectorsOn (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ S)
      (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) {x} := by
  rw [← compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph volume he he' hU hUΩ
    (hsurj := surjective_fderiv_of_openPartialHomeomorph he he' hU)]
  exact h.compCLMOfSubmersion (he.mono hU) hUΩ _

omit [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] in
/-- **The product of distributions does not depend on the coordinates**: for a smooth change of
variables `e`, if `S` and `T` satisfy Hörmander's condition at every point, then
`e^* (S T) = (e^* S) (e^* T)`. -/
theorem compCLMOfOpenPartialHomeomorph_product (h : ∀ y, NoOppositeCovectorsOn S T {y}) :
    compCLMOfOpenPartialHomeomorph e he he' hU hUΩ (S.product T h) =
      (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ S).product
        (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T)
        (fun x ↦ (h (e x)).compCLMOfOpenPartialHomeomorph he he' hU hUΩ) := by
  have hsurj := surjective_fderiv_of_openPartialHomeomorph he he' hU
  simp only [← compCLMOfSubmersion_eq_compCLMOfOpenPartialHomeomorph volume he he' hU hUΩ
    (hsurj := hsurj)]
  exact compCLMOfSubmersion_product (he.mono hU) hUΩ hsurj h

end ChangeOfVariables

end Distribution
