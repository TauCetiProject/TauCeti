/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.MeasureTheory.Function.Jacobian.Equiv
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

On a real inner product space, composition with `φ` is also the transpose of the pushforward for
the sesquilinear `L²` pairing, `∫ ⟪w ∘ φ, v⟫ = ∫ ⟪w, φ_* v⟫`
(`SchwartzMap.integral_inner_compCLM_eq`). The derivatives of `u ∘ g` along an orthonormal basis
`b` follow the chain rule `∂_{bᵢ} (u ∘ g) = ∑ⱼ ⟪bⱼ, Dg(·) bᵢ⟫ (∂_{bⱼ} u) ∘ g`
(`SchwartzMap.lineDerivOp_compCLM`). These are inputs of the Sobolev estimates for changes of
variables in `TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables`.

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
  have hcv := TauCeti.integral_comp_equiv_eq_integral_abs_det_fderiv_symm_smul μ
    (hψ.1.differentiable (by simp)) fun y ↦ f (φ.symm y) • u y
  simp only [Equiv.symm_apply_apply] at hcv
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

section InnerProduct

open scoped RealInnerProductSpace LineDeriv ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {g : E → E}

/-- **The chain rule on Schwartz functions.** For a map `g` of temperate growth, polynomially
bounded below, and an orthonormal basis `b`, the derivative of `u ∘ g` along `bᵢ` is
`∑ⱼ ⟪bⱼ, Dg(·) bᵢ⟫ (∂_{bⱼ} u) ∘ g`. -/
theorem lineDerivOp_compCLM {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (hg : g.HasTemperateGrowth) (hg' : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k)
    (u : 𝓢(E, F)) (i : ι) :
    ∂_{b i} (compCLM ℂ hg hg' u) =
      ∑ j, smulLeftCLM F (fun x ↦ ((⟪b j, fderiv ℝ g x (b i)⟫ : ℝ) : ℂ))
        (compCLM ℂ hg hg' (∂_{b j} u)) := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv, sum_apply]
  simp only [smulLeftCLM_apply_apply (hg.inner_fderiv_apply _ _), compCLM_apply]
  rw [fderiv_comp x u.differentiableAt (hg.1.differentiable (by simp) x),
    ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← b.sum_repr' (fderiv ℝ g x (b i))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, Complex.coe_smul, Function.comp_apply, lineDerivOp_apply_eq_fderiv]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {φ : E ≃ E}

open scoped InnerProductSpace in
/-- **Composition with `φ` is the transpose of the pushforward of densities** for the `L²` pairing:
`∫ ⟪w ∘ φ, v⟫ = ∫ ⟪w, φ_* v⟫`, where `(φ_* v)(y) = |det Dφ⁻¹(y)| v(φ⁻¹ y)`. -/
theorem integral_inner_compCLM_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (w v : 𝓢(E, F)) :
    ∫ x, ⟪compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) w x, v x⟫_ℂ =
      ∫ y, ⟪w y, pushforwardCLM ℂ φ hφ hψ v y⟫_ℂ := by
  have hcv := TauCeti.integral_comp_equiv_eq_integral_abs_det_fderiv_symm_smul volume
    (hψ.1.differentiable (by simp)) fun y ↦ ⟪w y, v (φ.symm y)⟫_ℂ
  simp only [Equiv.symm_apply_apply] at hcv
  simp only [compCLM_apply, Function.comp_apply, pushforwardCLM_apply, inner_smul_right, hcv]
  congr 1 with y

end InnerProduct

end SchwartzMap
