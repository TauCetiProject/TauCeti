/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Directional differentiation and linear maps on Schwartz space

Directional derivatives of a Schwartz function commute, since its second derivative is symmetric.
On the plane `ℂ`, the Laplacian is the sum of the second derivatives along `1` and `I`.

Applying a continuous real-linear map to the values of a Schwartz function commutes with
directional differentiation. In particular, real and imaginary parts, and the embedding of
real-valued functions into complex Schwartz space, commute with differentiation.

Multiplication by a continuous linear functional `L` satisfies the Leibniz rule
`∂_v (L f) = L ∂_v f + L v f`, and its iterate
`∂_v^(k+1) (L f) = L ∂_v^(k+1) f + (k + 1) L v ∂_v^k f`. On the Fourier side, multiplying a symbol
by `⟪h, ξ⟫` differentiates its kernel along `h`, so these identities control the derivatives of
the symbol of a differentiated kernel.
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

open scoped SchwartzMap LineDeriv

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Directional derivatives of Schwartz functions commute.** -/
theorem lineDerivOp_comm (f : 𝓢(V, F)) (v w : V) : ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) := by
  ext x
  have hd : DifferentiableAt ℝ (fderiv ℝ (f : V → F)) x :=
    ((f.smooth ⊤).fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  have hfun (u : V) : ⇑(∂_{u} f : 𝓢(V, F)) = fun y ↦ fderiv ℝ (f : V → F) y u :=
    funext fun y ↦ lineDerivOp_apply_eq_fderiv u f y
  rw [lineDerivOp_apply_eq_fderiv, lineDerivOp_apply_eq_fderiv, hfun, hfun,
    fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

open Laplacian in
/-- **The Laplacian on the plane in coordinates**: `Δ f = ∂₁² f + ∂₂² f` for a Schwartz function
`f` on `ℂ`, where `∂₁` and `∂₂` differentiate along `1` and `I`. -/
theorem laplacian_eq_lineDerivOp_one_I (f : 𝓢(ℂ, F)) :
    Δ f = ∂_{(1 : ℂ)} (∂_{(1 : ℂ)} f) + ∂_{Complex.I} (∂_{Complex.I} f) := by
  simp [laplacian_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]

/-- **The Leibniz rule for multiplication by a linear function**:
`∂_v (L f) = L ∂_v f + L v f` for a continuous linear functional `L`. -/
theorem lineDerivOp_smulLeftCLM_clm (L : V →L[ℝ] ℝ) (f : 𝓢(V, F)) (v : V) :
    ∂_{v} (smulLeftCLM F L f) = smulLeftCLM F L (∂_{v} f) + L v • f := by
  ext x
  simp [lineDerivOp_apply_eq_fderiv, smulLeftCLM_apply L.hasTemperateGrowth,
    fderiv_fun_smul L.differentiableAt f.differentiableAt]

/-- **The iterated Leibniz rule for multiplication by a linear function**:
`∂_v^(k+1) (L f) = L ∂_v^(k+1) f + (k + 1) L v ∂_v^k f` for a continuous linear functional `L`. -/
theorem iterate_lineDerivOp_smulLeftCLM_clm (L : V →L[ℝ] ℝ) (f : 𝓢(V, F)) (v : V) (k : ℕ) :
    (∂_{v})^[k + 1] (smulLeftCLM F L f) =
      smulLeftCLM F L ((∂_{v})^[k + 1] f) + ((k + 1) * L v) • (∂_{v})^[k] f := by
  induction k with
  | zero => simpa using lineDerivOp_smulLeftCLM_clm L f v
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_smul,
      lineDerivOp_smulLeftCLM_clm]
    simp only [Function.iterate_succ_apply']
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

end SchwartzMap
