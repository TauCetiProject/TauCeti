/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributions under linear changes of variables

Let `e` be a continuous linear automorphism of a real normed space `E`, and let `V`, `Ω` be open
sets with `e '' V ⊆ Ω`. A distribution `T` on `Ω` pulls back along `e` to the distribution

`(e^* T) φ = |det e|⁻¹ T (φ ∘ e⁻¹)`

on `V`. The factor `|det e|⁻¹` is the Jacobian of the change of variables `y = e x`, so on a
locally integrable function `f` the pullback is the function `f ∘ e`
(`Distribution.compCLMOfContinuousLinearEquiv_ofFun`), and the point mass at `y` pulls back to
`|det e|⁻¹` times the point mass at `e⁻¹ y`. Pulling back along `e` and then along `e⁻¹` gives
back `T`, and pulling back along a composite is the composite of the pullbacks.

Transport along a continuous linear equivalence `e : E' ≃L[ℝ] E` between different spaces pairs
a test function `φ` with `T` through `T (φ ∘ e⁻¹)`; the pullback above is `|det e|⁻¹` times it.
It moves a distribution to another carrier, for instance from `E × D` to the Euclidean product
`WithLp 2 (E × D)`.

Linear changes of variables are the first case of the coordinate invariance of operations on
distributions: they rescale localized Fourier transforms, which is how the wave front set
transforms under them.

## Main declarations

* `Distribution.compCLMOfContinuousLinearEquiv e hVO`: the pullback `T ↦ e^* T`, as a continuous
  linear map `𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(V, F)` preserving the order `n`.
* `Distribution.compCLMOfContinuousLinearEquiv_ofFun`: `e^*` sends the distribution of a locally
  integrable function `f` to that of `f ∘ e`, for any additive Haar measure.
* `Distribution.compCLMOfContinuousLinearEquiv_delta`: `e^* δ_y = |det e|⁻¹ δ_{e⁻¹ y}`.
* `Distribution.compCLMOfContinuousLinearEquiv_trans`,
  `Distribution.compCLMOfContinuousLinearEquiv_symm_apply_apply`: functoriality.
* `Distribution.complexPairing_compCLMOfContinuousLinearEquiv`: the complex-linear extension of
  `e^* T` to complex test functions is computed by the same formula.
* `Distribution.transportCLM e h`: for a continuous linear equivalence `e : E' ≃L[ℝ] E` between
  possibly different spaces, the transport `T ↦ (φ ↦ T (φ ∘ e⁻¹))` without Jacobian factor, with
  its support `Distribution.dsupport_transportCLM_subset` and its complex-linear extension
  `Distribution.complexPairing_transportCLM`, and functoriality
  `Distribution.transportCLM_trans`, `Distribution.transportCLM_symm_transportCLM`,
  `Distribution.transportCLM_transportCLM_symm`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (pullback of
  distributions by diffeomorphisms; here the diffeomorphism is linear).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W V Ω : Opens E} {n : ℕ∞}

section General

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The **pullback of a distribution along a linear change of variables**: for a continuous linear
automorphism `e` of `E` mapping `V` into `Ω`, a distribution `T` on `Ω` pulls back to the
distribution `φ ↦ |det e|⁻¹ T (φ ∘ e⁻¹)` on `V`. On the distribution of a locally integrable
function `f` it gives that of `f ∘ e` (`Distribution.compCLMOfContinuousLinearEquiv_ofFun`). -/
def compCLMOfContinuousLinearEquiv (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω) :
    𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(V, F) :=
  |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ •
    (e.transportTestFunction hVO).precompCompactConvergenceCLM F

/-- The pullback `e^* T` pairs a test function `φ` with `T` through `|det e|⁻¹ T (φ ∘ e⁻¹)`. -/
@[simp]
theorem compCLMOfContinuousLinearEquiv_apply (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω)
    (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(V, ℝ)) :
    compCLMOfContinuousLinearEquiv e hVO T φ =
      |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ • T (e.transportTestFunction hVO φ) :=
  (rfl)

/-- Pulling back along a composite of linear changes of variables is the composite of the
pullbacks. The hypothesis `h` on the composite follows from `h₁` and `h₂` as `h₂.comp h₁`. -/
theorem compCLMOfContinuousLinearEquiv_trans (e₁ e₂ : E ≃L[ℝ] E) (h₁ : MapsTo e₁ W V)
    (h₂ : MapsTo e₂ V Ω) (h : MapsTo (e₁.trans e₂) W Ω) (T : 𝓓'^{n}(Ω, F)) :
    compCLMOfContinuousLinearEquiv (e₁.trans e₂) h T =
      compCLMOfContinuousLinearEquiv e₁ h₁ (compCLMOfContinuousLinearEquiv e₂ h₂ T) := by
  ext φ
  have hdet : LinearMap.det ((e₁.trans e₂ : E ≃L[ℝ] E) : E →ₗ[ℝ] E) =
      LinearMap.det (e₂ : E →ₗ[ℝ] E) * LinearMap.det (e₁ : E →ₗ[ℝ] E) := by
    rw [ContinuousLinearEquiv.trans_toLinearEquiv, LinearEquiv.coe_trans, LinearMap.det_comp]
  simp only [compCLMOfContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.transportTestFunction_trans e₁ e₂ h₁ h₂ h, hdet, abs_mul, mul_inv,
    smul_smul, mul_comm]

/-- Pulling back along `e` and then along `e⁻¹` gives back the original distribution. -/
@[simp]
theorem compCLMOfContinuousLinearEquiv_symm_apply_apply (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (T : 𝓓'^{n}(Ω, F)) :
    compCLMOfContinuousLinearEquiv e.symm hOV (compCLMOfContinuousLinearEquiv e hVO T) = T := by
  ext φ
  have hdet : |LinearMap.det (e.symm : E →ₗ[ℝ] E)|⁻¹ * |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ = 1 := by
    rw [← mul_inv, ← abs_mul]
    simp
  simp only [compCLMOfContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.transportTestFunction_transportTestFunction_symm, smul_smul, hdet,
    one_smul]

end General

/-- The pullback of the point mass at `y` along `e` is `|det e|⁻¹` times the point mass at
`e⁻¹ y`. -/
theorem compCLMOfContinuousLinearEquiv_delta (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω) (y : E) :
    compCLMOfContinuousLinearEquiv e hVO (delta y : 𝓓'^{n}(Ω, ℝ)) =
      |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ • (delta (e.symm y) : 𝓓'^{n}(V, ℝ)) := by
  ext φ
  simp

/-- On the distribution of a function `f` locally integrable on `Ω`, the pullback along `e` is
the distribution of `f ∘ e`, for any additive Haar measure. -/
theorem compCLMOfContinuousLinearEquiv_ofFun [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω) (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F}
    (hf : LocallyIntegrableOn f Ω μ) :
    compCLMOfContinuousLinearEquiv e hVO (ofFun Ω f μ n) = ofFun V (fun x ↦ f (e x)) μ n := by
  ext φ
  rw [compCLMOfContinuousLinearEquiv_apply, ofFun_apply hf,
    ofFun_apply (hf.comp_continuousLinearEquiv_of_mapsTo e hVO)]
  -- Change variables `y = e x`: the image of `μ` under `e` is `|det e|⁻¹ • μ`.
  have hmap : μ.map e = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ (LinearEquiv.isUnit_det' _).ne_zero
  have hcov := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv
    fun y ↦ φ (e.symm y) • f y
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.symm_apply_apply] at hcov
  rw [← hcov, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  simp only [ContinuousLinearEquiv.transportTestFunction_apply]

/-- The complex-linear extension of the pullback `e^* T` of a complex distribution pairs a
complex test function `φ` with `T` through `|det e|⁻¹ T (φ ∘ e⁻¹)`. -/
theorem complexPairing_compCLMOfContinuousLinearEquiv (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω)
    (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(V, ℂ)) :
    (compCLMOfContinuousLinearEquiv e hVO T).complexPairing φ =
      (|LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ : ℝ) *
        T.complexPairing (e.transportTestFunction hVO φ) := by
  simp only [complexPairing_apply, compCLMOfContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.transportTestFunction_postcompCLM, Complex.real_smul]
  ring

/-! ### Transport between different spaces -/

section Transport

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Ω' : Opens E'}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The **transport of a distribution along a continuous linear equivalence** `e : E' ≃L[ℝ] E`
between possibly different spaces: a distribution `T` on `V` gives the distribution
`φ ↦ T (φ ∘ e⁻¹)` on any open set `Ω'` of `E'` with `e '' Ω' ⊆ V`. It is the transpose of the
transport of test functions `ContinuousLinearEquiv.transportTestFunction`, and carries no Jacobian
factor: for an automorphism `e` of `E`, the pullback `compCLMOfContinuousLinearEquiv e` is
`|det e|⁻¹` times it (`Distribution.compCLMOfContinuousLinearEquiv_eq_smul_transportCLM`).
Transport along `WithLp.prodContinuousLinearEquiv` moves a distribution on `E × D` to the
Euclidean product `WithLp 2 (E × D)`, where an inner product pairs positions with frequencies. -/
def transportCLM (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V) :
    𝓓'^{n}(V, F) →L[ℝ] 𝓓'^{n}(Ω', F) :=
  (e.transportTestFunction h).precompCompactConvergenceCLM F

/-- The transport of `T` along `e` pairs a test function `φ` with `T` through `T (φ ∘ e⁻¹)`. -/
@[simp]
theorem transportCLM_apply (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V) (T : 𝓓'^{n}(V, F))
    (φ : 𝓓^{n}(Ω', ℝ)) : transportCLM e h T φ = T (e.transportTestFunction h φ) :=
  (rfl)

/-- Transporting along a composite of continuous linear equivalences is transporting along each
in turn. The hypothesis `h` on the composite follows from `h₁` and `h₂` as `h₂.comp h₁`. -/
theorem transportCLM_trans {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {Ω'' : Opens E''} (e₁ : E'' ≃L[ℝ] E') (e₂ : E' ≃L[ℝ] E) (h₁ : MapsTo e₁ Ω'' Ω')
    (h₂ : MapsTo e₂ Ω' V) (h : MapsTo (e₁.trans e₂) Ω'' V) (T : 𝓓'^{n}(V, F)) :
    transportCLM (e₁.trans e₂) h T = transportCLM e₁ h₁ (transportCLM e₂ h₂ T) := by
  ext φ
  simp only [transportCLM_apply, ContinuousLinearEquiv.transportTestFunction_trans e₁ e₂ h₁ h₂ h]

/-- Transporting along `e` and then along `e⁻¹` gives back the original distribution. -/
@[simp]
theorem transportCLM_symm_transportCLM (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V)
    (h' : MapsTo e.symm V Ω') (T : 𝓓'^{n}(V, F)) :
    transportCLM e.symm h' (transportCLM e h T) = T := by
  ext φ
  simp

/-- Transporting along `e⁻¹` and then along `e` gives back the original distribution. -/
@[simp]
theorem transportCLM_transportCLM_symm (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V)
    (h' : MapsTo e.symm V Ω') (T : 𝓓'^{n}(Ω', F)) :
    transportCLM e h (transportCLM e.symm h' T) = T := by
  ext φ
  rw [transportCLM_apply, transportCLM_apply]
  congr 1
  ext y
  simp

/-- The pullback along an automorphism `e` of `E` is `|det e|⁻¹` times the transport along
`e`. -/
theorem compCLMOfContinuousLinearEquiv_eq_smul_transportCLM (e : E ≃L[ℝ] E)
    (hVO : MapsTo e V Ω) :
    (compCLMOfContinuousLinearEquiv e hVO : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(V, F)) =
      |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ • transportCLM e hVO :=
  (rfl)

/-- **Support of a transported distribution.** The support of the transport of `T` along `e`
lies in `e⁻¹ '' supp T`. -/
theorem dsupport_transportCLM_subset (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V) (T : 𝓓'^{n}(V, F)) :
    dsupport (transportCLM e h T) ⊆ e ⁻¹' dsupport T := by
  intro x hx
  by_contra hxT
  obtain ⟨s, hT, hs, hxs⟩ := (notMem_dsupport_iff _).1 hxT
  -- `T` vanishes on `s`, so its transport vanishes on `e⁻¹ '' s = e ⁻¹' s`.
  refine (notMem_dsupport_iff (f := transportCLM e h T) x).2
    ⟨e ⁻¹' s, fun φ hφ ↦ ?_, hs.preimage e.continuous, hxs⟩ hx
  rw [transportCLM_apply]
  refine hT _ ?_
  have hcoe : ⇑(e.transportTestFunction h φ) = φ ∘ e.symm := by
    ext y
    simp
  rw [hcoe]
  exact (tsupport_comp_subset_preimage φ e.symm.continuous).trans fun y hy ↦ by
    simpa using hφ hy

/-- The complex-linear extension of the transport of a complex distribution `T` along `e` pairs a
complex test function `φ` with `T` through `T (φ ∘ e⁻¹)`. -/
theorem complexPairing_transportCLM (e : E' ≃L[ℝ] E) (h : MapsTo e Ω' V) (T : 𝓓'(V, ℂ))
    (φ : 𝓓(Ω', ℂ)) :
    (transportCLM e h T).complexPairing φ = T.complexPairing (e.transportTestFunction h φ) := by
  simp only [complexPairing_apply, transportCLM_apply,
    ContinuousLinearEquiv.transportTestFunction_postcompCLM]

end Transport

end Distribution
