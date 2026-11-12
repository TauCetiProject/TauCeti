/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Laplacian
import TauCeti.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Worked examples for divergence-form Laplace regularity

Divergence-form Laplace regularity solves `Δξ = ∂ₛf + ∂ₜg` for real data `f, g` through the
Cauchy transform: with `h = f + i g`, the candidate solution is `ξ₀ = ½ Re (T h)`, and
`Δ (½ Re T h) = ∂ₛf + ∂ₜg` for compactly supported `C²` data
(`ContDiff.laplacian_half_re_cauchyTransform`). This file checks that the factor `½` is needed:
the plausible variant `Re T h` has Laplacian `2 (∂ₛf + ∂ₜg)`
(`ContDiff.laplacian_re_cauchyTransform`), which differs from the right-hand side for a bump
function.

The exponent bookkeeping on `log ‖z‖` is checked in `TauCeti.Analysis.Sobolev.Local.Examples`.

## Main results

* `exists_laplacian_re_cauchyTransform_ne`: the factor `½` cannot be dropped.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4.
-/

public noncomputable section

open Complex Laplacian

namespace TauCeti

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
