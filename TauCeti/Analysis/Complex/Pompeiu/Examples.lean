/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.Pompeiu.Laplacian
import TauCeti.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Normalisation checks for the Cauchy transform and divergence-form Laplace regularity

`TauCeti.cauchyTransform f w = π⁻¹ ∫ (w - z)⁻¹ • f z` is normalised to invert
`\bar∂ = (∂ₛ + i ∂ₜ) / 2`. The Cauchy–Pompeiu formula of `Pompeiu/Basic.lean` is instead written
with the constant `(2π)⁻¹` and the operator `D = ∂ₛ + i ∂ₜ = 2 \bar∂`. The identities comparing
the two normalisations, `TauCeti.fderiv_apply_one_add_I_smul_fderiv_apply_I` and
`TauCeti.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I_eq`, and those
for the transposed kernel `(z - w)⁻¹`, live beside the underlying APIs. This file checks the
consequences.

* The doubled operator: on compactly supported `C¹` maps the transform of `D u = 2 \bar∂ u` is
  `2 u`, so the transform inverts `D` only up to the factor `2` absorbed by `(2π)⁻¹`.
* The transposed kernel is not a right inverse of `\bar∂`, as witnessed by a smooth bump function.

Divergence-form Laplace regularity solves `Δξ = ∂ₛf + ∂ₜg` for real data `f, g` through the
Cauchy transform: with `h = f + i g`, the candidate solution is `ξ₀ = ½ Re (T h)`, and
`Δ (½ Re T h) = ∂ₛf + ∂ₜg` for compactly supported `C²` data
(`ContDiff.laplacian_half_re_cauchyTransform`). This file also checks that the factor `½` is
needed: the plausible variant `Re T h` has Laplacian `2 (∂ₛf + ∂ₜg)`
(`ContDiff.laplacian_re_cauchyTransform`), which differs from the right-hand side for a bump
function.

The exponent bookkeeping on `log ‖z‖` is checked in `TauCeti.Analysis.Sobolev.Local.Examples`.

## Main results

* `TauCeti.exists_conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul_ne`: the transposed
  kernel is not a right inverse of `\bar∂`.
* `TauCeti.exists_laplacian_re_cauchyTransform_ne`: the factor `½` cannot be dropped.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4.
-/

public noncomputable section

open MeasureTheory Complex Laplacian
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On compactly supported `C¹` maps the Cauchy transform of `D u = 2 \bar∂ u` is `2 u`: the
transform inverts `\bar∂`, so it inverts `D` only up to the factor `2`, which the Cauchy–Pompeiu
formula absorbs in its constant `(2π)⁻¹`. -/
example [CompleteSpace F] {u : ℂ → F} (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) :
    cauchyTransform ((2 : ℂ) • fun z ↦ conjWirtingerDeriv u z 1) = (2 : ℂ) • u := by
  rw [cauchyTransform_smul, funext (hc.cauchyTransform_conjWirtingerDeriv hu)]

/-- **The transposed kernel is not a right inverse of `\bar∂`.** There is a smooth compactly
supported `f : ℂ → ℂ`, a bump function equal to `1` at the origin, for which `\bar∂` of
`π⁻¹ ∫ (z - w)⁻¹ • f z` differs from `f` at the origin. -/
theorem exists_conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul_ne :
    ∃ f : ℂ → ℂ, HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧
      conjWirtingerDeriv (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (z - w)⁻¹ • f z) 0 1 ≠ f 0 := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport fun z ↦ (b z : ℂ) := b.hasCompactSupport.comp_left ofReal_zero
  have hs : ContDiff ℝ ∞ fun z ↦ (b z : ℂ) := ofRealCLM.contDiff.comp b.contDiff
  have h0 : (b 0 : ℂ) = 1 := by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self
    zero_le_one), ofReal_one]
  refine ⟨fun z ↦ (b z : ℂ), hc, hs, ?_⟩
  rw [hc.conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul (hs.of_le (by norm_num))]
  simp only [h0]
  norm_num

/-- **The factor `½` in the solution formula is needed.** There are real compactly supported
`C²` data for which `Re (T h)` does not solve `Δξ = ∂ₛf + ∂ₜg`. -/
theorem exists_laplacian_re_cauchyTransform_ne :
    ∃ f g : ℂ → ℝ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧ HasCompactSupport f ∧
      HasCompactSupport g ∧ ∃ w,
        Δ (fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re) w ≠
          fderiv ℝ f w 1 + fderiv ℝ g w I := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : ContDiff ℝ 2 (b : ℂ → ℝ) := b.contDiff
  have hbc : HasCompactSupport (b : ℂ → ℝ) := b.hasCompactSupport
  have hne : ∃ w, fderiv ℝ (b : ℂ → ℝ) w 1 ≠ 0 := by
    by_contra! H
    have h0 := hbc.eq_zero_of_fderiv_apply_eq_zero (hb.differentiable two_ne_zero) one_ne_zero H 0
    rw [b.one_of_mem_closedBall (by simp [b])] at h0
    exact one_ne_zero h0
  obtain ⟨w, hw⟩ := hne
  refine ⟨b, 0, hb, contDiff_const, hbc, HasCompactSupport.zero, w, ?_⟩
  rw [hb.laplacian_re_cauchyTransform (g := 0) contDiff_const hbc HasCompactSupport.zero w]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply, add_zero]
  intro h
  exact hw (by linarith)

end TauCeti
