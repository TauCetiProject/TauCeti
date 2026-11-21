/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal

/-!
# Pullback of tempered distributions along linear isometries

Let `A` be a linear isometry equivalence of a finite-dimensional real inner product space `E`, for
instance the reflection `x ↦ -x`. Its Jacobian determinant has absolute value `1`, so pushing a
Schwartz density forward along `A` is plain composition with `A⁻¹`
(`SchwartzMap.pushforwardCLM_linearIsometryEquiv`), and the pullback `A^*` of tempered
distributions (`TemperedDistribution.compCLM`) is the transpose of `f ↦ f ∘ A⁻¹`.

Since `𝓕 (f ∘ A) = (𝓕 f) ∘ A` for Schwartz functions, the pullback commutes with the Fourier
transform and its inverse (`TemperedDistribution.fourier_compCLM_linearIsometryEquiv`,
`TemperedDistribution.fourierInv_compCLM_linearIsometryEquiv`), and hence with every Fourier
multiplier whose symbol is invariant under `A`
(`TemperedDistribution.fourierMultiplierCLM_compCLM_linearIsometryEquiv`). The Bessel potential
`J^s`, whose symbol `(1 + ‖ξ‖²)^(s/2)` is radial, commutes with `A^*` for every real `s`
(`TemperedDistribution.besselPotential_compCLM_linearIsometryEquiv`). On `Lᵖ` functions the
pullback is composition with the measure-preserving map `A`
(`TemperedDistribution.compCLM_toTemperedDistribution_eq_compMeasurePreserving`). Together these
show that `A^*` preserves the Bessel-potential class `H^{s,p}` for every real `s` and every
`1 ≤ p ≤ ∞` (`TemperedDistribution.MemSobolev.compCLM_linearIsometryEquiv`), with the `Lᵖ`
representative of `J^s (A^* u)` the composition of that of `J^s u` with `A`; the norms of the
Bessel-potential spaces are therefore invariant under `A`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1.
-/

public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace SchwartzMap

variable (𝕜 : Type*) [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- Pushing a Schwartz density forward along a linear isometry equivalence `A` is composition with
`A⁻¹`: the Jacobian factor of `SchwartzMap.pushforwardCLM` is `1`. -/
theorem pushforwardCLM_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E)
    (hφ : (A.toHomeomorph.toEquiv : E → E).HasTemperateGrowth)
    (hψ : (A.toHomeomorph.toEquiv.symm : E → E).HasTemperateGrowth) :
    pushforwardCLM 𝕜 A.toHomeomorph.toEquiv hφ hψ (F := F) =
      compCLMOfContinuousLinearEquiv 𝕜 A.symm.toContinuousLinearEquiv := by
  ext f y
  have hd : fderiv ℝ (A.toHomeomorph.toEquiv.symm : E → E) y =
      (A.symm.toContinuousLinearEquiv : E →L[ℝ] E) := by
    simpa using A.symm.toContinuousLinearEquiv.fderiv (x := y)
  have hdet := Unitary.abs_det_eq_one (Unitary.linearIsometryEquiv.symm A.symm)
  rw [Unitary.coe_symm_linearIsometryEquiv_apply] at hdet
  rw [pushforwardCLM_apply, hd, hdet]
  simp

end SchwartzMap

namespace TemperedDistribution

variable [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  (A : E ≃ₗᵢ[ℝ] E) (hφ : (A.toHomeomorph.toEquiv : E → E).HasTemperateGrowth)
  (hψ : (A.toHomeomorph.toEquiv.symm : E → E).HasTemperateGrowth)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pullback of a tempered distribution along a linear isometry equivalence `A` is the
transpose of composition with `A⁻¹`: `(A^* T) f = T (f ∘ A⁻¹)`. -/
theorem compCLM_linearIsometryEquiv_apply_apply (T : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    compCLM F A.toHomeomorph.toEquiv hφ hψ T f =
      T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm.toContinuousLinearEquiv f) := by
  rw [compCLM_apply_apply, SchwartzMap.pushforwardCLM_linearIsometryEquiv]

/-- The pullback along a linear isometry equivalence commutes with the Fourier transform. -/
theorem fourier_compCLM_linearIsometryEquiv (T : 𝓢'(E, F)) :
    𝓕 (compCLM F A.toHomeomorph.toEquiv hφ hψ T) =
      compCLM F A.toHomeomorph.toEquiv hφ hψ (𝓕 T) := by
  ext f
  rw [fourier_apply, compCLM_linearIsometryEquiv_apply_apply,
    compCLM_linearIsometryEquiv_apply_apply, fourier_apply,
    SchwartzMap.fourier_compCLMOfContinuousLinearEquiv]

/-- The pullback along a linear isometry equivalence commutes with the inverse Fourier
transform. -/
theorem fourierInv_compCLM_linearIsometryEquiv (T : 𝓢'(E, F)) :
    𝓕⁻ (compCLM F A.toHomeomorph.toEquiv hφ hψ T) =
      compCLM F A.toHomeomorph.toEquiv hφ hψ (𝓕⁻ T) := by
  ext f
  rw [fourierInv_apply, compCLM_linearIsometryEquiv_apply_apply,
    compCLM_linearIsometryEquiv_apply_apply, fourierInv_apply,
    SchwartzMap.fourierInv_compCLMOfContinuousLinearEquiv]

/-- The pullback along a linear isometry equivalence `A` commutes with every Fourier multiplier
whose symbol `g` has temperate growth and is invariant under `A`. -/
theorem fourierMultiplierCLM_compCLM_linearIsometryEquiv {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hgA : ∀ ξ, g (A ξ) = g ξ) (T : 𝓢'(E, F)) :
    fourierMultiplierCLM F g (compCLM F A.toHomeomorph.toEquiv hφ hψ T) =
      compCLM F A.toHomeomorph.toEquiv hφ hψ (fourierMultiplierCLM F g T) := by
  have hgA' : g ∘ A.toHomeomorph.toEquiv = g := funext hgA
  rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
    ← fourierInv_compCLM_linearIsometryEquiv, compCLM_smulLeftCLM _ _ hg, hgA',
    fourier_compCLM_linearIsometryEquiv]

/-- The Bessel potential `J^s` commutes with the pullback along a linear isometry equivalence,
since its symbol `(1 + ‖ξ‖²)^(s/2)` is radial. -/
theorem besselPotential_compCLM_linearIsometryEquiv (s : ℝ) (T : 𝓢'(E, F)) :
    besselPotential E F s (compCLM F A.toHomeomorph.toEquiv hφ hψ T) =
      compCLM F A.toHomeomorph.toEquiv hφ hψ (besselPotential E F s T) :=
  fourierMultiplierCLM_compCLM_linearIsometryEquiv A hφ hψ (by fun_prop)
    (fun ξ ↦ by rw [A.norm_map]) T

/-- **Linear isometries preserve the Bessel-potential spaces.** If `J^s u` is the `Lᵖ` function
`v`, then `J^s (A^* u)` is the `Lᵖ` function `v ∘ A`, of the same `Lᵖ` norm. -/
theorem besselPotential_compCLM_linearIsometryEquiv_eq_compMeasurePreserving [CompleteSpace F]
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {T : 𝓢'(E, F)} {v : Lp F p (volume : Measure E)}
    (hT : besselPotential E F s T = v) :
    besselPotential E F s (compCLM F A.toHomeomorph.toEquiv hφ hψ T) =
      (Lp.compMeasurePreserving A A.measurePreserving v : 𝓢'(E, F)) := by
  rw [besselPotential_compCLM_linearIsometryEquiv, hT]
  exact compCLM_toTemperedDistribution_eq_compMeasurePreserving volume hφ hψ
    A.measurePreserving v

/-- The pullback along a linear isometry equivalence preserves membership in `H^{s,p}`, for every
real `s` and `1 ≤ p ≤ ∞`. -/
theorem MemSobolev.compCLM_linearIsometryEquiv [CompleteSpace F] {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {T : 𝓢'(E, F)} (hT : T.MemSobolev s p) :
    (compCLM F A.toHomeomorph.toEquiv hφ hψ T).MemSobolev s p := by
  obtain ⟨v, hv⟩ := hT
  exact ⟨_, besselPotential_compCLM_linearIsometryEquiv_eq_compMeasurePreserving A hφ hψ hv⟩

end TemperedDistribution
