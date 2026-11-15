/-
Copyright (c) 2026 Bastiaan J Braams and Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams, Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The sine substitution with an inverse square-root weight

On the monotone branch of sine, substituting `t = sin θ` replaces `dθ` by
`(1 - t²)^(-1/2) dt`. The integral identity and its integrability equivalence include
both endpoints `±π/2`; the resulting algebraic integrand can be singular at `±1`.
These formulas turn trigonometric elliptic integrals into algebraic integrals.

The integral identity adapts B. Braams' `Carlson.integral_legendre_eq` in
`lean-codes/Carlson/Elliptic/Standard.lean` (Apache-2.0), allowing either orientation
and arbitrary endpoints in the monotone branch. Integrability uses the same substitution.
-/

public section

open MeasureTheory Set Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sin_substitution_pullback {a b : ℝ}
    (ha : |a| ≤ π / 2) (hb : |b| ≤ π / 2) (g : ℝ → E) :
    EqOn (fun θ ↦ cos θ • ((1 - sin θ ^ 2) ^ (-1 / 2 : ℝ) • g (sin θ)))
      (fun θ ↦ g (sin θ)) (uIoo a b) := by
  intro θ hθ
  have hc := cos_pos_of_mem_uIoo ha hb hθ
  dsimp only
  rw [← cos_sq', neg_div, rpow_neg (sq_nonneg _), ← sqrt_eq_rpow, sqrt_sq hc.le]
  simp [smul_smul, hc.ne']

/-- The substitution `t = sin θ`, including the singular endpoints of the inverse
square-root weight. No integrability hypothesis is needed for this identity of total integrals. -/
theorem integral_comp_sin_eq_integral_rpow {a b : ℝ}
    (ha : |a| ≤ π / 2) (hb : |b| ≤ π / 2) (g : ℝ → E) :
    (∫ θ in a..b, g (sin θ)) =
      ∫ t in sin a..sin b, (1 - t ^ 2) ^ (-1 / 2 : ℝ) • g t := by
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := a) (b := b)
    (g := fun t ↦ (1 - t ^ 2) ^ (-1 / 2 : ℝ) • g t) continuous_sin.continuousOn
    (fun θ _ ↦ hasDerivAt_sin θ) (fun θ hθ ↦ ?_)
  · simp only [Function.comp_apply] at hsub
    exact (intervalIntegral.integral_congr_uIoo (sin_substitution_pullback ha hb g)).symm.trans hsub
  · exact (cos_pos_of_mem_uIoo ha hb hθ).le

/-- Integrability under the sine substitution. The equivalence includes the endpoints
`t = ±1`, where the inverse square-root weight is singular. -/
theorem intervalIntegrable_comp_sin_iff {a b : ℝ}
    (ha : |a| ≤ π / 2) (hb : |b| ≤ π / 2) (g : ℝ → E) :
    IntervalIntegrable (fun θ ↦ g (sin θ)) volume a b ↔
      IntervalIntegrable (fun t ↦ (1 - t ^ 2) ^ (-1 / 2 : ℝ) • g t)
        volume (sin a) (sin b) := by
  have hsub := intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg (a := a) (b := b)
    (g := fun t ↦ (1 - t ^ 2) ^ (-1 / 2 : ℝ) • g t) continuous_sin.continuousOn
    (fun θ _ ↦ hasDerivAt_sin θ) (fun θ hθ ↦ ?_)
  · simp only [Function.comp_apply] at hsub
    exact (intervalIntegrable_congr_uIoo (sin_substitution_pullback ha hb g)).symm.trans hsub
  · exact (cos_pos_of_mem_uIoo ha hb hθ).le

end TauCeti
