/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The one-dimensional energy estimate for traces

A compactly supported `C¹` real function has its squared value at the endpoint of a half-line
bounded by the integral of its value and derivative squared on that half-line. Integrating this
estimate over the transverse variables supplies the flat-boundary `H¹` trace inequality.

The estimate follows the fundamental-theorem-of-calculus proof of the trace theorem in
L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

namespace TauCeti

open MeasureTheory Set

/-- The endpoint value is controlled by the `H¹` energy on the right half-line. -/
theorem sq_le_integral_Ioi_sq_add_deriv_sq {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (a : ℝ) :
    g a ^ 2 ≤ ∫ t in Ioi a, g t ^ 2 + deriv g t ^ 2 := by
  have hd : ∀ t, deriv (fun s ↦ g s * g s) t = 2 * g t * deriv g t := by
    intro t
    exact ((hg.differentiable one_ne_zero t).hasDerivAt.mul
      (hg.differentiable one_ne_zero t).hasDerivAt).deriv.trans (by ring)
  have hi := (hs.mul_right (f' := g)).integral_Ioi_deriv_eq (hg.mul hg) a
  simp only [hd] at hi
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hs2 : HasCompactSupport (fun t ↦ g t ^ 2) :=
    hs.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hds2 : HasCompactSupport (fun t ↦ deriv g t ^ 2) :=
    hs.deriv.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hprod : Integrable (fun t ↦ 2 * g t * deriv g t) volume :=
    ((continuous_const.mul hg.continuous).mul hdc).integrable_of_hasCompactSupport
      (hs.mono (fun t ht hzero ↦ ht (by simp [hzero])))
  have henergy : Integrable (fun t ↦ g t ^ 2 + deriv g t ^ 2) volume :=
    ((hg.continuous.pow 2).add (hdc.pow 2)).integrable_of_hasCompactSupport (hs2.add hds2)
  calc
    g a ^ 2 = ∫ t in Ioi a, -(2 * g t * deriv g t) := by
      rw [integral_neg, hi]
      ring
    _ ≤ ∫ t in Ioi a, g t ^ 2 + deriv g t ^ 2 := by
      apply integral_mono hprod.neg.integrableOn henergy.integrableOn
      intro t
      dsimp only [Pi.neg_apply]
      nlinarith [sq_nonneg (g t + deriv g t)]

/-- A point value is bounded by the whole-line `H¹` energy. -/
theorem sq_le_integral_sq_add_deriv_sq {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (a : ℝ) :
    g a ^ 2 ≤ ∫ t, g t ^ 2 + deriv g t ^ 2 := by
  refine (sq_le_integral_Ioi_sq_add_deriv_sq hg hs a).trans ?_
  have hs2 : HasCompactSupport (fun t ↦ g t ^ 2) :=
    hs.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hds2 : HasCompactSupport (fun t ↦ deriv g t ^ 2) :=
    hs.deriv.mono (fun t ht hzero ↦ ht (by simp [hzero]))
  have hc := (hg.continuous.pow 2).add ((hg.continuous_deriv le_rfl).pow 2)
  exact setIntegral_le_integral (hc.integrable_of_hasCompactSupport (hs2.add hds2))
    (Filter.Eventually.of_forall fun t ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))

end TauCeti
