/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.FourierMultiplier
public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian

/-!
# Second derivatives of the planar Newtonian potential as Riesz transforms

For `φ : ℂ → F` smooth with compact support, the planar Newtonian potential
`u = G ⋆ φ`, `G z = -(2π)⁻¹ log ‖z‖` (`TauCeti.planarNewtonianKernel`), solves `-Δu = φ`. This file
shows that its second derivatives are compositions of Riesz transforms of `φ`:

`D²u(v, w) = R_v R_w φ` almost everywhere
(`TauCeti.coeFn_rieszTransform_rieszTransform_toLp_planarNewtonianKernel`).

This is the planar case of the identity `∂ᵢ∂ⱼ(Φ ⋆ φ) = RᵢRⱼ φ` for the fundamental solution `Φ` of
`-Δ`; for `n = 1` and `n ≥ 3` it is `TauCeti.coeFn_rieszTransform_rieszTransform_toLp`. On the
Fourier side both sides have symbol `-⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` times that of `φ`, but in the plane
the potential does not decay: it grows like `G z • ∫ φ`
(`TauCeti.tendsto_planarNewtonianKernel_convolution_sub_cocompact`). The identity holds because
this growth is slow enough for
`TauCeti.coeFn_rieszTransform_rieszTransform_toLp_of_laplacian_eq_neg`, which asks in dimension two
for `u z / ‖z‖ → 0` and `Du z → 0` at infinity:

* `‖u z‖ ≤ ‖u z - G z • ∫ φ‖ + (2π)⁻¹ |log ‖z‖| ‖∫ φ‖`, and `log ‖z‖ / ‖z‖ → 0`;
* `Du = G ⋆ Dφ`, and `Dφ` has integral zero, so `Du z = (G ⋆ Dφ) z - G z • ∫ Dφ → 0`.

## Main declarations

* `TauCeti.coeFn_rieszTransform_rieszTransform_toLp_planarNewtonianKernel`:
  `D²(G ⋆ φ)(v, w) = R_v R_w φ`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.4.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Module Topology
open scoped Convolution ContDiff Laplacian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {φ : ℂ → F}

/-- The planar Newtonian potential grows sublinearly: `‖G ⋆ φ‖ / ‖z‖ → 0` at infinity, because
it differs from `G z • ∫ φ` by a function tending to zero and `log ‖z‖ / ‖z‖ → 0`. -/
private theorem tendsto_rpow_mul_norm_planarNewtonianKernel_convolution
    (hc : HasCompactSupport φ) :
    Tendsto (fun z => ‖z‖ ^ ((finrank ℝ ℂ : ℝ) / 2 - 2) * ‖(planarNewtonianKernel ⋆ φ) z‖)
      (cocompact ℂ) (𝓝 0) := by
  have hexp : ((finrank ℝ ℂ : ℕ) : ℝ) / 2 - 2 = -1 := by
    rw [Complex.finrank_real_complex]
    norm_num
  rw [hexp]
  set u := planarNewtonianKernel ⋆ φ
  set M := ‖∫ w, φ w‖
  have hinv : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop
  have hlog : Tendsto (fun z : ℂ => |Real.log ‖z‖ / ‖z‖|) (cocompact ℂ) (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_norm_cocompact_atTop (E := ℂ))
    simpa [Function.comp_def] using h.abs
  have hlim := (hinv.mul (tendsto_planarNewtonianKernel_convolution_sub_cocompact hc).norm).add
    ((hlog.const_mul (2 * Real.pi)⁻¹).mul_const M)
  simp only [norm_zero, mul_zero, zero_mul, add_zero] at hlim
  refine squeeze_zero (fun z => by positivity) (fun z => ?_) hlim
  rw [Real.rpow_neg_one]
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  calc ‖z‖⁻¹ * ‖u z‖
      ≤ ‖z‖⁻¹ * (‖u z - planarNewtonianKernel z • ∫ w, φ w‖ +
          ‖planarNewtonianKernel z • ∫ w, φ w‖) :=
        mul_le_mul_of_nonneg_left (norm_le_norm_sub_add _ _) (by positivity)
    _ = ‖z‖⁻¹ * ‖u z - planarNewtonianKernel z • ∫ w, φ w‖ +
          (2 * Real.pi)⁻¹ * |Real.log ‖z‖ / ‖z‖| * M := by
        rw [mul_add, norm_smul, planarNewtonianKernel_def, Real.norm_eq_abs, abs_mul, abs_neg,
          abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_div,
          abs_of_pos hz0]
        ring

/-- The derivative of the planar Newtonian potential tends to zero at infinity: it is the
potential of `Dφ`, which has integral zero. -/
private theorem tendsto_rpow_mul_norm_fderiv_planarNewtonianKernel_convolution
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Tendsto (fun z => ‖z‖ ^ ((finrank ℝ ℂ : ℝ) / 2 - 1) *
      ‖fderiv ℝ (planarNewtonianKernel ⋆ φ) z‖) (cocompact ℂ) (𝓝 0) := by
  have hexp : ((finrank ℝ ℂ : ℕ) : ℝ) / 2 - 1 = 0 := by
    rw [Complex.finrank_real_complex]
    norm_num
  simp only [hexp, Real.rpow_zero, one_mul]
  -- `Du = G ⋆ Dφ`, where the convolution of the operator-valued `Dφ` is along scalar
  -- multiplication.
  have hL : ((lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR ℂ) = lsmul ℝ ℝ := by
    ext
    simp
  have hD : fderiv ℝ (planarNewtonianKernel ⋆ φ) = planarNewtonianKernel ⋆ fderiv ℝ φ := by
    funext z
    rw [(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) locallyIntegrable_planarNewtonianKernel
      hφ z).fderiv, hL]
  have h := (tendsto_planarNewtonianKernel_convolution_sub_cocompact
    (hc.fderiv (𝕜 := ℝ))).norm
  rw [integral_fderiv_eq_zero_of_hasCompactSupport hφ hc, norm_zero] at h
  simpa [hD] using h

variable [CompleteSpace F]

/-- **Second derivatives of the planar Newtonian potential are Riesz transforms.** For `φ`
smooth with compact support on `ℂ`, the Newtonian potential `u = G ⋆ φ`, the solution of
`-Δu = φ` with the logarithmic kernel `G z = -(2π)⁻¹ log ‖z‖`, has second derivatives

`D²u(v, w) = R_v R_w φ`

almost everywhere, where `R_v` is the Riesz transform with symbol `-i ⟪ξ, v⟫ / ‖ξ‖`. -/
theorem coeFn_rieszTransform_rieszTransform_toLp_planarNewtonianKernel (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v w : ℂ) :
    rieszTransform F v (rieszTransform F w
        ((hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).toLp φ)) =ᵐ[volume]
      fun z => iteratedFDeriv ℝ 2 (planarNewtonianKernel ⋆ φ) z ![v, w] :=
  coeFn_rieszTransform_rieszTransform_toLp_of_laplacian_eq_neg
    (contDiff_planarNewtonianKernel_convolution hφ hc)
    (laplacian_planarNewtonianKernel_convolution (hφ.of_le (by simp)) hc) _ hc
    (tendsto_rpow_mul_norm_planarNewtonianKernel_convolution hc)
    (tendsto_rpow_mul_norm_fderiv_planarNewtonianKernel_convolution (hφ.of_le (by simp)) hc) v w

end TauCeti
