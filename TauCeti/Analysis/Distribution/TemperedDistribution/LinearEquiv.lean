/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.LinearIsometry
import TauCeti.Topology.Algebra.Module.Equiv.Basic

/-!
# Tempered distributions under linear changes of variables

Let `e` be a continuous linear automorphism of a finite-dimensional real normed space `E`. A
tempered distribution `T` pulls back along `e` to the tempered distribution

`(e^* T) f = |det e|⁻¹ T (f ∘ e⁻¹)`

(`TemperedDistribution.compCLMOfContinuousLinearEquiv`), the case of a linear map of the pullback
`TemperedDistribution.compCLM` along a change of variables. On the distribution of a Schwartz
function `u` it is the distribution of `u ∘ e`.

When `E` is an inner product space and `A` is a linear isometry, `|det A| = 1` and the pullback is
`(A^* T) f = T (f ∘ A⁻¹)`. It then commutes with the Fourier transform, since the Fourier
transform of `u ∘ A` is `𝓕 u ∘ A`. Hence it carries the Fourier multiplier with symbol `g` to the
one with symbol `g ∘ A`, so commutes with every Fourier multiplier whose symbol is invariant under
`A`, in particular with the Bessel potentials `J^s`, whose symbol
`(1 + ‖ξ‖ ^ 2) ^ (s / 2)` only depends on `‖ξ‖`. Since `A` preserves Lebesgue measure, the pullback
of an `Lᵖ` function is the `Lᵖ` function `u ∘ A`, of the same norm. Together these say that `A^*`
preserves every Bessel-potential space `H^{s,p}`; the resulting isometries of `H^{s,p}` are built
in `TauCeti.Analysis.Sobolev.BesselPotential.LinearIsometry`. The main example is the reflection
`x ↦ -x`, which relates the bilinear pairings of Schwartz functions on the Fourier side and on the
space side.

## Main declarations

* `TemperedDistribution.compCLMOfContinuousLinearEquiv e`: the pullback `T ↦ e^* T`, with
  `compCLMOfContinuousLinearEquiv_apply_apply`, its value on Schwartz functions
  `compCLMOfContinuousLinearEquiv_toTemperedDistributionCLM`, and functoriality
  `compCLMOfContinuousLinearEquiv_trans`, `compCLMOfContinuousLinearEquiv_refl` and
  `compCLMOfContinuousLinearEquiv_symm_apply_apply`,
  `compCLMOfContinuousLinearEquiv_apply_symm_apply`.
* `TemperedDistribution.compCLMOfContinuousLinearEquiv_linearIsometryEquiv_apply_apply`: for a
  linear isometry, `(A^* T) f = T (f ∘ A⁻¹)`.
* `TemperedDistribution.fourier_compCLMOfContinuousLinearEquiv` and
  `TemperedDistribution.fourierInv_compCLMOfContinuousLinearEquiv`: the Fourier transform and its
  inverse commute with `A^*`.
* `TemperedDistribution.fourierMultiplierCLM_compCLMOfContinuousLinearEquiv`: `A^*` carries the
  Fourier multiplier with symbol `g` to the one with symbol `g ∘ A`, so it commutes with every
  Fourier multiplier with an `A`-invariant symbol, and in particular
  `TemperedDistribution.besselPotential_compCLMOfContinuousLinearEquiv`: every Bessel potential.
* `compCLMOfContinuousLinearEquiv_toTemperedDistribution_eq_compMeasurePreserving`: on `Lᵖ`, the
  pullback is precomposition `Lp.compMeasurePreserving`.
* `TemperedDistribution.MemSobolev.compCLMOfContinuousLinearEquiv`: `A^*` preserves `H^{s,p}`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1 (the Fourier
  transform under linear changes of variables).
-/

public noncomputable section

open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal

namespace TemperedDistribution

variable {E F : Type*}

section Pullback

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

variable (F) in
/-- The **pullback of a tempered distribution along a linear change of variables**: for a
continuous linear automorphism `e` of `E`, `(e^* T) f = |det e|⁻¹ T (f ∘ e⁻¹)`
(`TemperedDistribution.compCLMOfContinuousLinearEquiv_apply_apply`). On the distribution of a
Schwartz function `u` it gives that of `u ∘ e`
(`TemperedDistribution.compCLMOfContinuousLinearEquiv_toTemperedDistributionCLM`). -/
def compCLMOfContinuousLinearEquiv (e : E ≃L[ℝ] E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  compCLM F e.toEquiv
    (by rw [ContinuousLinearEquiv.coe_toEquiv]; exact e.hasTemperateGrowth)
    (by rw [ContinuousLinearEquiv.coe_toEquiv_symm]; exact e.symm.hasTemperateGrowth)

/-- The pullback `e^* T` pairs a Schwartz function `f` with `T` through
`|det e|⁻¹ T (f ∘ e⁻¹)`. -/
theorem compCLMOfContinuousLinearEquiv_apply_apply (e : E ≃L[ℝ] E) (T : 𝓢'(E, F))
    (f : 𝓢(E, ℂ)) :
    compCLMOfContinuousLinearEquiv F e T f =
      ((|LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ : ℝ) : ℂ) •
        T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f) := by
  rw [compCLMOfContinuousLinearEquiv, compCLM_apply_apply, ← map_smul]
  congr 1
  ext y
  have hd : fderiv ℝ (e.toEquiv.symm : E → E) y = (e.symm : E →L[ℝ] E) := by
    rw [ContinuousLinearEquiv.coe_toEquiv_symm]
    exact e.symm.fderiv
  have hdet : LinearMap.det ((e.symm : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      (LinearMap.det (e : E →ₗ[ℝ] E))⁻¹ :=
    LinearEquiv.det_coe_symm (e : E ≃ₗ[ℝ] E)
  rw [SchwartzMap.pushforwardCLM_apply, hd, ContinuousLinearMap.det, hdet, abs_inv]
  simp

/-- Pulling back along a composite of linear changes of variables is the composite of the
pullbacks. -/
theorem compCLMOfContinuousLinearEquiv_trans (e₁ e₂ : E ≃L[ℝ] E) (T : 𝓢'(E, F)) :
    compCLMOfContinuousLinearEquiv F (e₁.trans e₂) T =
      compCLMOfContinuousLinearEquiv F e₁ (compCLMOfContinuousLinearEquiv F e₂ T) := by
  have h : (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv := by
    ext x
    simp only [Equiv.trans_apply, ContinuousLinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.trans_apply]
  simp only [compCLMOfContinuousLinearEquiv, h]
  rw [← ContinuousLinearMap.comp_apply, ← compCLM_trans]

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compCLMOfContinuousLinearEquiv_refl (T : 𝓢'(E, F)) :
    compCLMOfContinuousLinearEquiv F (ContinuousLinearEquiv.refl ℝ E) T = T := by
  have h : (ContinuousLinearEquiv.refl ℝ E).toEquiv = Equiv.refl E := by
    ext x
    simp only [ContinuousLinearEquiv.coe_toEquiv, ContinuousLinearEquiv.coe_refl', id_eq,
      Equiv.refl_apply]
  simp only [compCLMOfContinuousLinearEquiv, h, compCLM_refl, ContinuousLinearMap.id_apply]

/-- Pulling back along `e` and then along `e⁻¹` gives back the original distribution. -/
@[simp]
theorem compCLMOfContinuousLinearEquiv_symm_apply_apply (e : E ≃L[ℝ] E) (T : 𝓢'(E, F)) :
    compCLMOfContinuousLinearEquiv F e.symm (compCLMOfContinuousLinearEquiv F e T) = T := by
  simp only [compCLMOfContinuousLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_symm,
    LinearEquiv.toEquiv_symm]
  exact compCLM_symm_compCLM _ _ _ T

/-- Pulling back along `e⁻¹` and then along `e` gives back the original distribution. -/
@[simp]
theorem compCLMOfContinuousLinearEquiv_apply_symm_apply (e : E ≃L[ℝ] E) (T : 𝓢'(E, F)) :
    compCLMOfContinuousLinearEquiv F e (compCLMOfContinuousLinearEquiv F e.symm T) = T := by
  simp only [compCLMOfContinuousLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_symm,
    LinearEquiv.toEquiv_symm]
  exact compCLM_compCLM_symm _ _ _ T

end Pullback

section Embedding

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The pullback of the distribution of a Schwartz function `u` is the distribution of `u ∘ e`,
for every additive Haar measure. -/
@[simp]
theorem compCLMOfContinuousLinearEquiv_toTemperedDistributionCLM (μ : Measure E)
    [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E) (u : 𝓢(E, F)) :
    compCLMOfContinuousLinearEquiv F e (toTemperedDistributionCLM E F μ u) =
      toTemperedDistributionCLM E F μ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e u) := by
  rw [compCLMOfContinuousLinearEquiv, compCLM_toTemperedDistributionCLM]
  refine congrArg _ (SchwartzMap.ext fun x ↦ ?_)
  rw [SchwartzMap.compCLM_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.coe_toEquiv]

end Embedding

/-! ### Linear isometries -/

section LinearIsometry

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- The pullback along a linear isometry `A` is `(A^* T) f = T (f ∘ A⁻¹)`: the Jacobian factor is
`|det A|⁻¹ = 1`. -/
@[simp]
theorem compCLMOfContinuousLinearEquiv_linearIsometryEquiv_apply_apply (A : E ≃ₗᵢ[ℝ] E)
    (T : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv T f =
      T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm.toContinuousLinearEquiv f) := by
  have hdet : |LinearMap.det (A.toContinuousLinearEquiv : E →ₗ[ℝ] E)| = 1 := by
    rw [← LinearMap.normDet_eq_abs_det]
    exact A.toLinearIsometry.normDet_eq_one
  rw [compCLMOfContinuousLinearEquiv_apply_apply, hdet, inv_one, Complex.ofReal_one, one_smul,
    LinearIsometryEquiv.toContinuousLinearEquiv_symm]

variable [MeasurableSpace E] [BorelSpace E]

/-- The Fourier transform commutes with the pullback along a linear isometry:
`𝓕 (A^* T) = A^* (𝓕 T)`. -/
theorem fourier_compCLMOfContinuousLinearEquiv (A : E ≃ₗᵢ[ℝ] E) (T : 𝓢'(E, F)) :
    𝓕 (compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv T) =
      compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv (𝓕 T) := by
  ext f
  simp only [fourier_apply, compCLMOfContinuousLinearEquiv_linearIsometryEquiv_apply_apply]
  congr 1
  ext ξ
  rw [SchwartzMap.fourier_compCLMOfContinuousLinearEquiv_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The inverse Fourier transform commutes with the pullback along a linear isometry:
`𝓕⁻ (A^* T) = A^* (𝓕⁻ T)`. -/
theorem fourierInv_compCLMOfContinuousLinearEquiv (A : E ≃ₗᵢ[ℝ] E) (T : 𝓢'(E, F)) :
    𝓕⁻ (compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv T) =
      compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv (𝓕⁻ T) := by
  ext f
  simp only [fourierInv_apply, compCLMOfContinuousLinearEquiv_linearIsometryEquiv_apply_apply]
  congr 1
  ext ξ
  rw [SchwartzMap.fourierInv_apply_eq_fourier_neg,
    SchwartzMap.fourier_compCLMOfContinuousLinearEquiv_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.fourierInv_apply_eq_fourier_neg]
  simp

end TVS

variable [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The pullback along a linear isometry `A` intertwines Fourier multipliers, carrying the
symbol `g` to `g ∘ A`: `T_{g ∘ A} (A^* T) = A^* (T_g T)`. In particular a Fourier multiplier whose
symbol is invariant under `A` commutes with `A^*`. -/
theorem fourierMultiplierCLM_compCLMOfContinuousLinearEquiv (A : E ≃ₗᵢ[ℝ] E) (g : E → ℂ)
    (T : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g ∘ A) (compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv T) =
      compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv (fourierMultiplierCLM F g T) := by
  by_cases hg : g.HasTemperateGrowth
  · have hcomp : g ∘ A.toContinuousLinearEquiv.toEquiv = g ∘ A := by
      rw [ContinuousLinearEquiv.coe_toEquiv, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
      fourier_compCLMOfContinuousLinearEquiv, compCLMOfContinuousLinearEquiv,
      ← hcomp, ← compCLM_smulLeftCLM _ _ hg, ← compCLMOfContinuousLinearEquiv,
      fourierInv_compCLMOfContinuousLinearEquiv]
  · have hgA : ¬(g ∘ A).HasTemperateGrowth :=
      A.toContinuousLinearEquiv.hasTemperateGrowth_comp_iff.not.mpr hg
    ext u
    simp [fourierMultiplierCLM_apply_apply, SchwartzMap.smulLeftCLM, hg, hgA]

/-- The Bessel potential `J^s` commutes with the pullback along a linear isometry. -/
theorem besselPotential_compCLMOfContinuousLinearEquiv (A : E ≃ₗᵢ[ℝ] E) (s : ℝ) (T : 𝓢'(E, F)) :
    besselPotential E F s (compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv T) =
      compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv (besselPotential E F s T) := by
  have h := fourierMultiplierCLM_compCLMOfContinuousLinearEquiv A
    (fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) T
  rwa [show (fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) ∘ A =
    fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) from funext fun x ↦ by simp] at h

variable [CompleteSpace F]

/-- On the distribution of an `Lᵖ` function `u`, the pullback along a linear isometry `A` is the
distribution of the `Lᵖ` function `u ∘ A`. -/
theorem compCLMOfContinuousLinearEquiv_toTemperedDistribution_eq_compMeasurePreserving
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : E ≃ₗᵢ[ℝ] E) (u : Lp F p (volume : Measure E)) :
    compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv (u : 𝓢'(E, F)) =
      (Lp.compMeasurePreserving A A.measurePreserving u : 𝓢'(E, F)) := by
  ext f
  rw [compCLMOfContinuousLinearEquiv, compCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.integral_pushforwardCLM_smul]
  refine integral_congr_ae ((Lp.coeFn_compMeasurePreserving u A.measurePreserving).mono
    fun x hx ↦ ?_)
  dsimp only
  rw [hx, Function.comp_apply, ContinuousLinearEquiv.coe_toEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The pullback along a linear isometry preserves the Bessel-potential space `H^{s,p}`. -/
theorem MemSobolev.compCLMOfContinuousLinearEquiv {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {T : 𝓢'(E, F)} (hT : MemSobolev s p T) (A : E ≃ₗᵢ[ℝ] E) :
    MemSobolev s p (compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv T) := by
  obtain ⟨u, hu⟩ := hT
  exact ⟨Lp.compMeasurePreserving A A.measurePreserving u, by
    rw [besselPotential_compCLMOfContinuousLinearEquiv, hu,
      compCLMOfContinuousLinearEquiv_toTemperedDistribution_eq_compMeasurePreserving]⟩

end LinearIsometry

end TemperedDistribution
