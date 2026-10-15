/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Norm bounds and pointwise operators on bounded continuous functions

This file records norm estimates for operations on bounded continuous functions, and the operator
of pointwise application of a bounded continuous family of continuous linear maps.

The main estimate, `TauCeti.norm_boundedContinuousFunction_comp_le`, bounds the sup norm of the
postcomposition `N ∘ f` of a bounded continuous function `f` by an `ε`-Lipschitz map `N` by
`‖N 0‖ + ε * ‖f‖`. Thus a globally Lipschitz nonlinearity maps bounded continuous functions to
bounded ones with an explicit affine norm bound. In `TauCeti.Analysis.ODE.LyapunovPerron.Basic` it
supplies the uniform bound on the forcing term `s ↦ N (γ s)` that makes the Lyapunov–Perron
integral converge and defines the Lyapunov–Perron operator on bounded continuous curves.

`BoundedContinuousFunction.applyCLM` applies a bounded continuous family `φ` of continuous linear
maps pointwise, `(φ, h) ↦ (t ↦ φ t (h t))`, as a continuous bilinear map, and
`BoundedContinuousFunction.norm_applyCLM_apply_le` bounds the operator norm of `applyCLM φ`
by `‖φ‖`.
The derivative of a superposition operator `f ↦ G ∘ f` at `f` is `applyCLM` of the family
`t ↦ G' (f t)` of derivatives of `G`; see
`TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction`.
-/

public section

open scoped NNReal BoundedContinuousFunction

namespace TauCeti

variable {T X Y : Type*} [TopologicalSpace T] [SeminormedAddCommGroup X]
  [SeminormedAddCommGroup Y]
  {N : X → Y} {ε : ℝ≥0}

/-- Postcomposition by an `ε`-Lipschitz map `N` has norm at most
`‖N 0‖ + ε * ‖f‖`. -/
theorem norm_boundedContinuousFunction_comp_le (hN : LipschitzWith ε N) (f : T →ᵇ X) :
    ‖f.comp N hN‖ ≤ ‖N 0‖ + ε * ‖f‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_
  have h := hN.dist_le_mul (f t) 0
  rw [dist_eq_norm, dist_zero_right] at h
  have ht := f.norm_coe_le_norm t
  have := norm_sub_norm_le (N (f t)) (N 0)
  simp only [BoundedContinuousFunction.comp_apply]
  nlinarith [ε.coe_nonneg]

end TauCeti

namespace BoundedContinuousFunction

variable {α 𝕜 X Y : Type*} [TopologicalSpace α] [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Pointwise application `(φ, h) ↦ (t ↦ φ t (h t))` of a bounded continuous family `φ` of
continuous linear maps to a bounded continuous function `h`, as a continuous bilinear map. -/
noncomputable def applyCLM : (α →ᵇ (X →L[𝕜] Y)) →L[𝕜] (α →ᵇ X) →L[𝕜] α →ᵇ Y :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜
      (fun (φ : α →ᵇ (X →L[𝕜] Y)) (h : α →ᵇ X) ↦
        ofNormedAddCommGroup (fun t ↦ φ t (h t)) (φ.continuous.clm_apply h.continuous)
        (‖φ‖ * ‖h‖) fun t ↦
          (φ t).le_of_opNorm_le_of_le (φ.norm_coe_le_norm t) (h.norm_coe_le_norm t))
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
      (fun _ _ _ ↦ by ext; simp))
    1 fun φ h ↦ by
      rw [LinearMap.mk₂_apply, one_mul]
      exact norm_ofNormedAddCommGroup_le _ (by positivity) _

@[simp]
theorem applyCLM_apply (φ : α →ᵇ (X →L[𝕜] Y)) (h : α →ᵇ X) (t : α) :
    applyCLM φ h t = φ t (h t) :=
  (rfl)

/-- Pointwise application of `φ` has operator norm at most the sup norm of `φ`. -/
theorem norm_applyCLM_apply_le (φ : α →ᵇ (X →L[𝕜] Y)) : ‖applyCLM φ‖ ≤ ‖φ‖ :=
  (applyCLM φ).opNorm_le_bound (norm_nonneg φ) fun h ↦ (norm_le (by positivity)).2 fun t ↦
    (φ t).le_of_opNorm_le_of_le (φ.norm_coe_le_norm t) (h.norm_coe_le_norm t)

end BoundedContinuousFunction
