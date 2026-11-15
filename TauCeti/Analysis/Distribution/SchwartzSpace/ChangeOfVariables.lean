/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Pushforward of Schwartz densities along a change of variables

Let `φ : E ≃ E` be a bijection of a finite-dimensional real normed space such that `φ` and `φ⁻¹`
both have temperate growth: they are smooth and all their derivatives grow at most polynomially.
Examples are diffeomorphisms whose derivatives of positive order, and those of their inverses, are
bounded, and polynomial automorphisms such as the shear `(x, y) ↦ (x, y + x³)` of `ℝ²`.

The **pushforward** of a Schwartz function `f`, regarded as a density, is

`(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)`.

It is a continuous linear map of Schwartz space (`SchwartzMap.pushforwardCLM`): composition with
`φ⁻¹` is Mathlib's `SchwartzMap.compCLM`, and the Jacobian factor has temperate growth. By the
change of variables formula it is the transpose of composition with `φ`:

`∫ (φ_* f)(y) • u(y) dμ(y) = ∫ f(x) • u(φ x) dμ(x)`

for every function `u` and every additive Haar measure `μ`
(`SchwartzMap.integral_pushforwardCLM_smul`). This is how tempered distributions are pulled back
along `φ`, by transposition.

The pushforward is functorial: `(χ ∘ φ)_* = χ_* ∘ φ_*` by the chain rule for the Jacobian
determinant (`SchwartzMap.pushforwardCLM_trans`), and the identity pushes forward to the identity
(`SchwartzMap.pushforwardCLM_refl`). Multiplication by `g ∘ φ` before the pushforward is
multiplication by `g` after it (`SchwartzMap.pushforwardCLM_smulLeftCLM`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 and §7.1.
-/

public noncomputable section

open MeasureTheory

namespace SchwartzMap

variable (𝕜 : Type*) {E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {φ : E ≃ E}

/-- The **pushforward of Schwartz densities** along a bijection `φ` such that `φ` and `φ⁻¹` have
temperate growth: `(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)`, as a continuous linear map of Schwartz
space. It is the transpose of composition with `φ`
(`SchwartzMap.integral_pushforwardCLM_smul`). -/
def pushforwardCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  smulLeftCLM F (fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : 𝕜)) ∘L
    compCLM 𝕜 hψ (hφ.exists_norm_le_of_leftInverse φ.right_inv)

@[simp]
theorem pushforwardCLM_apply (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, F)) (y : E) :
    pushforwardCLM 𝕜 φ hφ hψ f y = ((|(fderiv ℝ φ.symm y).det| : ℝ) : 𝕜) • f (φ.symm y) := by
  rw [pushforwardCLM, ContinuousLinearMap.comp_apply,
    smulLeftCLM_apply_apply (g := fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : 𝕜))
      ((RCLike.hasTemperateGrowth_ofReal 𝕜).comp (hφ.abs_det_fderiv_symm hψ)), compCLM_apply,
    Function.comp_apply]

/-- **The pushforward is the transpose of composition.** For every function `u` and every
additive Haar measure `μ`, `∫ (φ_* f)(y) • u(y) dμ(y) = ∫ f(x) • u(φ x) dμ(x)`. No integrability
is needed: both sides are the two sides of the change of variables formula. -/
theorem integral_pushforwardCLM_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, 𝕜)) (u : E → G) :
    ∫ y, pushforwardCLM 𝕜 φ hφ hψ f y • u y ∂μ = ∫ x, f x • u (φ x) ∂μ := by
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ MeasurableSet.univ
    (fun y _ ↦ (hψ.1.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
    φ.symm.injective.injOn fun x ↦ f x • u (φ x)
  rw [Set.image_univ_of_surjective φ.symm.surjective] at hcv
  simp only [Measure.restrict_univ, Equiv.apply_symm_apply] at hcv
  rw [hcv]
  congr 1 with y
  rw [pushforwardCLM_apply, smul_assoc, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-- **Functoriality of the pushforward**: `(χ ∘ φ)_* = χ_* ∘ φ_*`, by the chain rule for the
Jacobian determinant. -/
theorem pushforwardCLM_trans {χ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hχ : (χ : E → E).HasTemperateGrowth)
    (hχs : (χ.symm : E → E).HasTemperateGrowth) (h₁ : (φ.trans χ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans χ).symm : E → E).HasTemperateGrowth) :
    pushforwardCLM 𝕜 (φ.trans χ) h₁ h₂ (F := F) =
      pushforwardCLM 𝕜 χ hχ hχs ∘L pushforwardCLM 𝕜 φ hφ hψ := by
  ext f y
  have hd : fderiv ℝ ((φ.trans χ).symm) y = fderiv ℝ φ.symm (χ.symm y) ∘L fderiv ℝ χ.symm y :=
    fderiv_comp y (hψ.1.differentiable (by simp) _) (hχs.1.differentiable (by simp) _)
  rw [ContinuousLinearMap.comp_apply, pushforwardCLM_apply, pushforwardCLM_apply,
    pushforwardCLM_apply, hd, ContinuousLinearMap.det_comp, abs_mul, RCLike.ofReal_mul, mul_comm,
    mul_smul, Equiv.symm_trans_apply]

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem pushforwardCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth) :
    pushforwardCLM 𝕜 (Equiv.refl E) h₁ h₂ (F := F) = ContinuousLinearMap.id 𝕜 _ := by
  ext f y
  simp

/-- Multiplying by `g ∘ φ` and then pushing forward along `φ` is pushing forward and then
multiplying by `g`. -/
theorem pushforwardCLM_smulLeftCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {g : E → 𝕜} (hg : g.HasTemperateGrowth)
    (f : 𝓢(E, F)) :
    pushforwardCLM 𝕜 φ hφ hψ (smulLeftCLM F (g ∘ φ) f) =
      smulLeftCLM F g (pushforwardCLM 𝕜 φ hφ hψ f) := by
  ext y
  rw [pushforwardCLM_apply, smulLeftCLM_apply_apply (hg.comp hφ), smulLeftCLM_apply_apply hg,
    pushforwardCLM_apply, Function.comp_apply, Equiv.apply_symm_apply, smul_comm]

end SchwartzMap
