/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import TauCeti.Analysis.Calculus.PlaneShear

/-!
# Shears of the plane on Schwartz space

For `g : ℝ → ℝ` of temperate growth the shear `φ(x, y) = (x, y + g x)` of `TauCeti.planeShear` has
temperate growth, and so does its inverse, the shear along `-g`. Precomposition with it is therefore
a continuous linear map on Schwartz space (`TauCeti.compPlaneShearCLM`), with the chain rule
`∂_v (u ∘ φ) = (∂_v u) ∘ φ + g'(x) v₀ (∂_y u) ∘ φ` (`TauCeti.lineDerivOp_compPlaneShearCLM_apply`).

## Main declarations

* `TauCeti.hasTemperateGrowth_planeShear`: the shear along `g` of temperate growth has temperate
  growth.
* `TauCeti.compPlaneShearCLM`: precomposition with the shear on Schwartz functions.
* `TauCeti.lineDerivOp_compPlaneShearCLM_apply`: its chain rule.
-/

public section

noncomputable section

open scoped SchwartzMap LineDeriv

namespace TauCeti

variable {g : ℝ → ℝ}

@[fun_prop]
theorem hasTemperateGrowth_planeShear (hg : g.HasTemperateGrowth) :
    (planeShear g).HasTemperateGrowth := by
  have h0 : (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0).HasTemperateGrowth :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasTemperateGrowth
  rw [funext (planeShear_def g)]
  fun_prop

/-- For `g` of temperate growth, a point is bounded polynomially in terms of its image under the
shear: `‖p‖ ≤ C (1 + ‖planeShear g p‖) ^ k`. -/
theorem exists_norm_le_mul_one_add_norm_planeShear_pow (hg : g.HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖planeShear g p‖) ^ k := by
  obtain ⟨k, C, hC⟩ := (hasTemperateGrowth_planeShear hg.neg).2 0
  exact ⟨k, C, fun p ↦ by simpa [planeShear_neg_planeShear] using hC (planeShear g p)⟩

variable (𝕜 : Type*) [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F]

/-- **Precomposition with the shear** `(x, y) ↦ (x, y + g x)` on Schwartz functions, for `g` of
temperate growth. -/
def compPlaneShearCLM (g : ℝ → ℝ) (hg : g.HasTemperateGrowth) :
    𝓢(EuclideanSpace ℝ (Fin 2), F) →L[𝕜] 𝓢(EuclideanSpace ℝ (Fin 2), F) :=
  SchwartzMap.compCLM 𝕜 (hasTemperateGrowth_planeShear hg)
    (exists_norm_le_mul_one_add_norm_planeShear_pow hg)

variable {𝕜}

@[simp]
theorem compPlaneShearCLM_apply (hg : g.HasTemperateGrowth) (u : 𝓢(EuclideanSpace ℝ (Fin 2), F))
    (p : EuclideanSpace ℝ (Fin 2)) : compPlaneShearCLM 𝕜 g hg u p = u (planeShear g p) := by
  simp [compPlaneShearCLM]

theorem coe_compPlaneShearCLM (hg : g.HasTemperateGrowth) (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) :
    ⇑(compPlaneShearCLM 𝕜 g hg u) = u ∘ planeShear g :=
  funext <| compPlaneShearCLM_apply hg u

@[simp]
theorem compPlaneShearCLM_zero :
    compPlaneShearCLM 𝕜 0 .zero = ContinuousLinearMap.id 𝕜 𝓢(EuclideanSpace ℝ (Fin 2), F) := by
  ext u p
  simp

/-- Precomposition with shears composes by adding their functions. -/
theorem compPlaneShearCLM_comp_compPlaneShearCLM {g₁ g₂ : ℝ → ℝ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    (compPlaneShearCLM 𝕜 g₂ hg₂).comp (compPlaneShearCLM 𝕜 g₁ hg₁ :
        𝓢(EuclideanSpace ℝ (Fin 2), F) →L[𝕜] _) =
      compPlaneShearCLM 𝕜 (g₁ + g₂) (hg₁.add hg₂) := by
  ext u p
  simp

/-- **The chain rule for the shear**: `∂_v (u ∘ φ) = (∂_v u) ∘ φ + g'(x) v₀ (∂_y u) ∘ φ`. -/
theorem lineDerivOp_compPlaneShearCLM_apply (hg : g.HasTemperateGrowth)
    (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) (v p : EuclideanSpace ℝ (Fin 2)) :
    ∂_{v} (compPlaneShearCLM 𝕜 g hg u) p =
      ∂_{v} u (planeShear g p) + (deriv g (p 0) * v 0) •
        ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u (planeShear g p) := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, coe_compPlaneShearCLM]
  exact fderiv_comp_planeShear_apply u.differentiableAt
    (hg.1.differentiable (by simp) (p 0)) v

end TauCeti
