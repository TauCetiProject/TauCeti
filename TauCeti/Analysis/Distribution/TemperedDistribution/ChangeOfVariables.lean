/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Pullback of tempered distributions along a change of variables

Let `φ : E ≃ E` be a bijection of a finite-dimensional real normed space such that `φ` and `φ⁻¹`
both have temperate growth, for instance a diffeomorphism whose derivatives of positive order, and
those of its inverse, are bounded. A tempered distribution `T` pulls back along `φ` to

`(φ^* T) f = T (φ_* f)`,

where `(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)` is the pushforward of Schwartz densities
`SchwartzMap.pushforwardCLM`. This is `TemperedDistribution.compCLM φ`, a continuous linear map
`𝓢'(E, F) →L[ℂ] 𝓢'(E, F)`. The Jacobian factor makes it extend composition with `φ`: for a Schwartz
function, or a function of temperate growth, `u`, the pullback of the distribution of `u` is the
distribution of `u ∘ φ`, for every additive Haar measure (`compCLM_toTemperedDistributionCLM`,
`compCLM_toTemperedDistribution`). The point mass at `y` pulls back to `|det Dφ⁻¹(y)|` times the
point mass at `φ⁻¹ y` (`compCLM_delta`), so the point mass at `φ x` pulls back to `|det Dφ(x)|⁻¹`
times the point mass at `x` (`compCLM_delta_apply`).

The pullback is contravariantly functorial, `(χ ∘ φ)^* = φ^* ∘ χ^*` (`compCLM_trans`), so pulling
back along `φ⁻¹` inverts it (`compCLM_symm_compCLM`, `compCLM_compCLM_symm`). It turns
multiplication by `g` into multiplication by `g ∘ φ` (`compCLM_smulLeftCLM`).

This is the global change of variables on `𝓢'` against which the Bessel-potential spaces `H^s`,
which are subspaces of `𝓢'`, are compared under diffeomorphisms of `E`. It needs no bound on the
derivatives beyond temperate growth: the shear `(x, y) ↦ (x, y + x³)` of `ℝ²` and its inverse are
polynomial, with unbounded derivatives, and they pull back tempered distributions.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 and §7.1.
-/

public noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E ≃ E}

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

variable (F) in
/-- The **pullback of tempered distributions** along a bijection `φ` such that `φ` and `φ⁻¹` have
temperate growth: `(φ^* T) f = T (φ_* f)`, the transpose of the pushforward of Schwartz densities
`(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)`. On functions it is composition with `φ`
(`TemperedDistribution.compCLM_toTemperedDistribution`). -/
def compCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp _ (SchwartzMap.pushforwardCLM ℂ φ hφ hψ)

@[simp]
theorem compCLM_apply_apply (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (T : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    compCLM F φ hφ hψ T f = T (SchwartzMap.pushforwardCLM ℂ φ hφ hψ f) :=
  (rfl)

/-- **Functoriality of the pullback**: `(χ ∘ φ)^* = φ^* ∘ χ^*`. -/
theorem compCLM_trans {χ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hχ : (χ : E → E).HasTemperateGrowth)
    (hχs : (χ.symm : E → E).HasTemperateGrowth) (h₁ : (φ.trans χ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans χ).symm : E → E).HasTemperateGrowth) :
    compCLM F (φ.trans χ) h₁ h₂ = compCLM F φ hφ hψ ∘L compCLM F χ hχ hχs := by
  ext T f
  simp [SchwartzMap.pushforwardCLM_trans ℂ hφ hψ hχ hχs h₁ h₂]

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth) :
    compCLM F (Equiv.refl E) h₁ h₂ = ContinuousLinearMap.id ℂ _ := by
  ext T f
  simp

/-- Pulling back along `φ` and then along `φ⁻¹` gives back the distribution. -/
@[simp]
theorem compCLM_symm_compCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (T : 𝓢'(E, F)) :
    compCLM F φ.symm hψ hφ (compCLM F φ hφ hψ T) = T := by
  ext f
  simp

/-- Pulling back along `φ⁻¹` and then along `φ` gives back the distribution. -/
@[simp]
theorem compCLM_compCLM_symm (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (T : 𝓢'(E, F)) :
    compCLM F φ hφ hψ (compCLM F φ.symm hψ hφ T) = T := by
  ext f
  simp

/-- The pullback of `g T` is `(g ∘ φ) φ^* T`. -/
theorem compCLM_smulLeftCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (T : 𝓢'(E, F)) :
    compCLM F φ hφ hψ (smulLeftCLM F g T) = smulLeftCLM F (g ∘ φ) (compCLM F φ hφ hψ T) := by
  ext f
  simp [SchwartzMap.smulLeftCLM_pushforwardCLM ℂ hφ hψ hg]

end TVS

section Normed

variable [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [MeasurableSpace E]
  [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The pullback of the distribution of a Schwartz function `u` is the distribution of `u ∘ φ`,
for every additive Haar measure. -/
@[simp]
theorem compCLM_toTemperedDistributionCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (u : 𝓢(E, F)) :
    compCLM F φ hφ hψ (SchwartzMap.toTemperedDistributionCLM E F μ u) =
      SchwartzMap.toTemperedDistributionCLM E F μ
        (SchwartzMap.compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u) := by
  ext f
  simp only [compCLM_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    SchwartzMap.integral_pushforwardCLM_smul, SchwartzMap.compCLM_apply, Function.comp_apply]

/-- The pullback of the distribution of a function `u` of temperate growth is the distribution
of `u ∘ φ`, for every additive Haar measure. -/
@[simp]
theorem compCLM_toTemperedDistribution (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {u : E → F} (hu : u.HasTemperateGrowth) :
    compCLM F φ hφ hψ (hu.toTemperedDistribution μ) = (hu.comp hφ).toTemperedDistribution μ := by
  ext f
  simp only [compCLM_apply_apply, Function.HasTemperateGrowth.toTemperedDistribution_apply,
    SchwartzMap.integral_pushforwardCLM_smul, Function.comp_apply]

end Normed

/-- The point mass at `y` pulls back to `|det Dφ⁻¹(y)|` times the point mass at `φ⁻¹ y`. -/
@[simp]
theorem compCLM_delta (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (y : E) :
    compCLM ℂ φ hφ hψ (delta y) = ((|(fderiv ℝ φ.symm y).det| : ℝ) : ℂ) • delta (φ.symm y) := by
  ext f
  simp

/-- The point mass at `φ x` pulls back to `|det Dφ(x)|⁻¹` times the point mass at `x`. -/
theorem compCLM_delta_apply (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (x : E) :
    compCLM ℂ φ hφ hψ (delta (φ x)) = ((|(fderiv ℝ φ x).det|⁻¹ : ℝ) : ℂ) • delta x := by
  have h := φ.det_fderiv_symm_mul_det_fderiv (y := φ x) (hφ.1.differentiable (by simp) _)
    (hψ.1.differentiable (by simp) _)
  rw [Equiv.symm_apply_apply] at h
  rw [compCLM_delta, Equiv.symm_apply_apply, eq_inv_of_mul_eq_one_left h, abs_inv]

end TemperedDistribution
