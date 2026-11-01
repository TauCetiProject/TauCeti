/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Directional derivative estimates for scalar multiplication

Multiplying a map by a real scalar function separates its derivative into a principal part and
an error involving the derivative of the scalar function. The estimate below bounds the sum of
the squared derivative norms in two arbitrary directions, as used in cutoff energy estimates.
It requires differentiability only at the point where the estimate is evaluated.

A product `c • f` of two factors that vanish at a point and are Lipschitz near it, in the sense
of the difference estimate satisfied by strictly differentiable maps, is strictly differentiable
there with derivative zero. Neither factor needs to be differentiable: this applies, for
instance, to a norm, which is Lipschitz but need not be differentiable.

## Main results

* `TauCeti.cutoff_sq_mul_norm_fderiv_sq_le`: the two-direction cutoff derivative estimate.
* `TauCeti.hasStrictFDerivAt_smul_of_isBigO_sub`: a product of two Lipschitz factors vanishing
  at a point is strictly differentiable there, with derivative zero.
-/

public section

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The squared derivative energy in two directions, weighted by a real scalar function, is
bounded by the energy of the scalar multiple and the scalar derivative error. No compact support
or normalization of the directions is needed. -/
theorem cutoff_sq_mul_norm_fderiv_sq_le {u : E → V} {χ : E → ℝ} {z : E}
    (hu : DifferentiableAt ℝ u z) (hχ : DifferentiableAt ℝ χ z) (e₁ e₂ : E) :
    χ z ^ 2 * (‖fderiv ℝ u z e₁‖ ^ 2 + ‖fderiv ℝ u z e₂‖ ^ 2) ≤
      2 * (‖fderiv ℝ (χ • u) z e₁‖ ^ 2 + ‖fderiv ℝ (χ • u) z e₂‖ ^ 2) +
      2 * (fderiv ℝ χ z e₁ ^ 2 + fderiv ℝ χ z e₂ ^ 2) * ‖u z‖ ^ 2 := by
  have hderiv (e : E) : fderiv ℝ (χ • u) z e =
      χ z • fderiv ℝ u z e + fderiv ℝ χ z e • u z := by
    simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, add_comm] using
      congrArg (fun L : E →L[ℝ] V => L e) (fderiv_smul hχ hu)
  have hdir (e : E) :
      χ z ^ 2 * ‖fderiv ℝ u z e‖ ^ 2 ≤
        2 * ‖fderiv ℝ (χ • u) z e‖ ^ 2 + 2 * fderiv ℝ χ z e ^ 2 * ‖u z‖ ^ 2 := by
    have heq : χ z • fderiv ℝ u z e =
        fderiv ℝ (χ • u) z e - fderiv ℝ χ z e • u z := by rw [hderiv]; abel
    have hnorm := norm_sub_le (fderiv ℝ (χ • u) z e) (fderiv ℝ χ z e • u z)
    rw [← heq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    have hsq := mul_self_le_mul_self (by positivity) hnorm
    nlinarith only [hsq, sq_abs (χ z), sq_abs (fderiv ℝ χ z e),
      add_sq_le (a := ‖fderiv ℝ (χ • u) z e‖) (b := |fderiv ℝ χ z e| * ‖u z‖)]
  nlinarith only [hdir e₁, hdir e₂]

section Strict

open Asymptotics Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A product `c • f` of two factors that vanish at `x` and satisfy the difference estimate of a
strictly differentiable map near `x` is strictly differentiable at `x`, with derivative zero.
Neither factor needs to be differentiable. -/
theorem hasStrictFDerivAt_smul_of_isBigO_sub {c : E → 𝕜} {f : E → F} {x : E}
    (hc : (fun p : E × E ↦ c p.1 - c p.2) =O[𝓝 (x, x)] fun p ↦ p.1 - p.2)
    (hf : (fun p : E × E ↦ f p.1 - f p.2) =O[𝓝 (x, x)] fun p ↦ p.1 - p.2)
    (hcx : c x = 0) (hfx : f x = 0) :
    HasStrictFDerivAt (fun y ↦ c y • f y) (0 : E →L[𝕜] F) x := by
  rw [hasStrictFDerivAt_iff_isLittleO]
  -- Split `c y • f y - c y' • f y'` into `c y • (f y - f y') + (c y - c y') • f y'`; in each
  -- term one factor tends to zero and the other is controlled by `y - y'`.
  have h₁ : (fun p : E × E ↦ c p.1 • (f p.1 - f p.2)) =o[𝓝 (x, x)] fun p ↦ p.1 - p.2 := by
    have hc₁ : Tendsto (fun p : E × E ↦ c p.1) (𝓝 (x, x)) (𝓝 0) := by
      have h := (continuousAt_of_isBigO_sub hc).tendsto.comp (continuous_fst.tendsto (x, x))
      rwa [hcx] at h
    simpa using ((isLittleO_one_iff 𝕜).2 hc₁).smul_isBigO hf
  have h₂ : (fun p : E × E ↦ (c p.1 - c p.2) • f p.2) =o[𝓝 (x, x)] fun p ↦ p.1 - p.2 := by
    have hf₂ : Tendsto (fun p : E × E ↦ f p.2) (𝓝 (x, x)) (𝓝 0) := by
      have h := (continuousAt_of_isBigO_sub hf).tendsto.comp (continuous_snd.tendsto (x, x))
      rwa [hfx] at h
    have h := hc.norm_right.smul_isLittleO ((isLittleO_one_iff ℝ).2 hf₂)
    simp only [smul_eq_mul, mul_one] at h
    exact h.of_norm_right
  refine (h₁.add h₂).congr_left fun p ↦ ?_
  simp only [smul_sub, sub_smul, zero_apply, sub_zero]
  abel

end Strict

end TauCeti

end
