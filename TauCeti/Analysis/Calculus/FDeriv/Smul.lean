/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Directional derivative estimates for scalar multiplication

Multiplying a map by a scalar function separates its derivative into a principal part and an
error involving the derivative of the scalar function. For a real scalar function, the estimate
below bounds the sum of the squared derivative norms in two arbitrary directions, as used in
cutoff energy estimates. It requires differentiability only at the point where the estimate is
evaluated.

A product `c • f` of two factors that vanish at a point and are Lipschitz near it, in the sense
of the difference estimate satisfied by strictly differentiable maps, is strictly differentiable
there with derivative zero. Neither factor needs to be differentiable: this applies, for
instance, to a norm, which is Lipschitz but need not be differentiable. As in Mathlib's Leibniz
rule `fderiv_smul`, the scalar factor may take values in a normed ring acting on the codomain,
not only in the base field.

At a zero of a differentiable scalar factor, continuity of the vector factor suffices for
Fréchet differentiability of their product, including scalars in a normed algebra.

## Main results

* `HasFDerivWithinAt.smul_of_eq_zero` and `HasFDerivAt.smul_of_eq_zero`: the scalar-multiplication
  rule at a zero of the scalar factor, with only continuity of the vector factor.
* `TauCeti.fderiv_smul_apply`: the Leibniz rule for the derivative of a scalar multiple, applied to
  a direction.
* `TauCeti.cutoff_sq_mul_norm_fderiv_sq_le`: the two-direction cutoff derivative estimate.
* `TauCeti.hasStrictFDerivAt_smul_of_isBigO_sub`: a product of two Lipschitz factors vanishing
  at a point is strictly differentiable there, with derivative zero.
-/

public section

namespace TauCeti

section Leibniz

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {𝕜' : Type*} [NormedRing 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- At a zero of a differentiable scalar factor, the vector factor need only be continuous
within the parameter set to differentiate their scalar multiple. Scalars may take values in a
normed algebra over the base field. -/
theorem _root_.HasFDerivWithinAt.smul_of_eq_zero {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'} {f : E → F}
    {s : Set E} {x : E} (hc : HasFDerivWithinAt c c' s x)
    (hf : ContinuousWithinAt f s x) (hc0 : c x = 0) :
    HasFDerivWithinAt (fun y ↦ c y • f y) (c'.smulRight (f x)) s x := by
  have hd := HasFDerivWithinAt.clm_apply_of_eq_zero
    (ContinuousAt.comp_continuousWithinAt
      (ContinuousLinearMap.lsmul 𝕜 𝕜' (E := F)).flip.continuous.continuousAt hf)
    hc hc0
  exact hd.congr_fderiv (by ext v; rfl)

/-- At a zero of a differentiable scalar factor, the vector factor need only be continuous
to differentiate their scalar multiple. Scalars may take values in a normed algebra over the
base field. -/
theorem _root_.HasFDerivAt.smul_of_eq_zero {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'} {f : E → F}
    {x : E} (hc : HasFDerivAt c c' x) (hf : ContinuousAt f x) (hc0 : c x = 0) :
    HasFDerivAt (fun y ↦ c y • f y) (c'.smulRight (f x)) x := by
  rw [← hasFDerivWithinAt_univ]
  exact hc.hasFDerivWithinAt.smul_of_eq_zero hf.continuousWithinAt hc0

/-- **The Leibniz rule for the directional derivative of a scalar multiple.** The derivative of
`c • f` at `x` in the direction `e` is `c x` times that of `f`, plus that of `c` times `f x`. -/
theorem fderiv_smul_apply {c : E → 𝕜'} {f : E → F} {x : E} (hc : DifferentiableAt 𝕜 c x)
    (hf : DifferentiableAt 𝕜 f x) (e : E) :
    fderiv 𝕜 (c • f) x e = c x • fderiv 𝕜 f x e + fderiv 𝕜 c x e • f x := by
  simp [fderiv_smul hc hf]

end Leibniz

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
  have hdir (e : E) :
      χ z ^ 2 * ‖fderiv ℝ u z e‖ ^ 2 ≤
        2 * ‖fderiv ℝ (χ • u) z e‖ ^ 2 + 2 * fderiv ℝ χ z e ^ 2 * ‖u z‖ ^ 2 := by
    have heq : χ z • fderiv ℝ u z e =
        fderiv ℝ (χ • u) z e - fderiv ℝ χ z e • u z := by
      rw [fderiv_smul_apply hχ hu, add_sub_cancel_right]
    have hnorm := norm_sub_le (fderiv ℝ (χ • u) z e) (fderiv ℝ χ z e • u z)
    rw [← heq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    have hsq := mul_self_le_mul_self (by positivity) hnorm
    nlinarith only [hsq, sq_abs (χ z), sq_abs (fderiv ℝ χ z e),
      add_sq_le (a := ‖fderiv ℝ (χ • u) z e‖) (b := |fderiv ℝ χ z e| * ‖u z‖)]
  nlinarith only [hdir e₁, hdir e₂]

section Strict

open Asymptotics Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {R : Type*} [NormedRing R]
  [Module R F] [IsBoundedSMul R F]

/-- A product `c • f` of two factors that vanish at `x` and satisfy the difference estimate of a
strictly differentiable map near `x` is strictly differentiable at `x`, with derivative zero.
Neither factor needs to be differentiable, and the scalar factor `c` may take values in any normed
ring acting boundedly on the codomain of `f`. -/
theorem hasStrictFDerivAt_smul_of_isBigO_sub {c : E → R} {f : E → F} {x : E}
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
