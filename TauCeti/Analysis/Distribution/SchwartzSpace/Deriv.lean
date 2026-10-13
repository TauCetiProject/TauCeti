/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Directional differentiation and linear maps on Schwartz space

Applying a continuous real-linear map to the values of a Schwartz function commutes with
directional differentiation. In particular, real and imaginary parts, and the embedding of
real-valued functions into complex Schwartz space, commute with differentiation.

On a real inner product space, multiplication by the linear function `ξ ↦ ⟪ξ, h⟫` satisfies the
Leibniz rule `∂_v (⟪·, h⟫ f) = ⟪·, h⟫ ∂_v f + ⟪v, h⟫ f`, and its iterate
`∂_v^(k+1) (⟪·, h⟫ f) = ⟪·, h⟫ ∂_v^(k+1) f + (k + 1) ⟪v, h⟫ ∂_v^k f`. On the Fourier side,
multiplying a symbol by `⟪ξ, h⟫` differentiates its kernel along `h`, so these identities control
the derivatives of the symbol of a differentiated kernel.
-/

public section

namespace TauCeti

open scoped SchwartzMap LineDeriv

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Directional differentiation commutes with a continuous real-linear map on the values
of a Schwartz function. -/
@[simp]
theorem lineDerivOp_postcompCLM (v : E) (L : F →L[ℝ] G) (φ : 𝓢(E, F)) :
    ∂_{v} (φ.postcompCLM L) = (∂_{v} φ).postcompCLM L := by
  have hfun : ⇑(φ.postcompCLM L) = L ∘ φ :=
    funext (SchwartzMap.postcompCLM_apply L φ)
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun,
    (L.hasFDerivAt.comp x φ.differentiableAt.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, SchwartzMap.postcompCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

end TauCeti

namespace SchwartzMap

open scoped RealInnerProductSpace SchwartzMap LineDeriv

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Leibniz rule for multiplication by a linear function**:
`∂_v (⟪·, h⟫ f) = ⟪·, h⟫ ∂_v f + ⟪v, h⟫ f`. -/
theorem lineDerivOp_smulLeftCLM_inner (f : 𝓢(V, F)) (v h : V) :
    ∂_{v} (smulLeftCLM F (inner ℝ · h) f) =
      smulLeftCLM F (inner ℝ · h) (∂_{v} f) + ⟪v, h⟫ • f := by
  have hg : (inner ℝ · h : V → ℝ).HasTemperateGrowth := by fun_prop
  have hi : (inner ℝ · h : V → ℝ) = innerSL ℝ h := funext fun y ↦ real_inner_comm _ _
  ext x
  rw [lineDerivOp_apply_eq_fderiv, smulLeftCLM_apply hg, add_apply, smul_apply,
    smulLeftCLM_apply_apply hg, lineDerivOp_apply_eq_fderiv, fderiv_fun_smul
    (by rw [hi]; exact (innerSL ℝ h).differentiableAt) f.differentiableAt, hi,
    ContinuousLinearMap.fderiv]
  simp [real_inner_comm]

/-- **The iterated Leibniz rule for multiplication by a linear function**:
`∂_v^(k+1) (⟪·, h⟫ f) = ⟪·, h⟫ ∂_v^(k+1) f + (k + 1) ⟪v, h⟫ ∂_v^k f`. -/
theorem iterate_lineDerivOp_smulLeftCLM_inner (f : 𝓢(V, F)) (v h : V) (k : ℕ) :
    (∂_{v})^[k + 1] (smulLeftCLM F (inner ℝ · h) f) =
      smulLeftCLM F (inner ℝ · h) ((∂_{v})^[k + 1] f) + ((k + 1) * ⟪v, h⟫) • (∂_{v})^[k] f := by
  induction k with
  | zero => simpa using lineDerivOp_smulLeftCLM_inner f v h
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_smul,
      lineDerivOp_smulLeftCLM_inner]
    simp only [Function.iterate_succ_apply']
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

end SchwartzMap
