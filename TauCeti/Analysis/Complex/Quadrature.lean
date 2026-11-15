/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Schwarz
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Quadrature error for kernel-weighted holomorphic integrals

Given a scalar kernel `κ : V → ℂ` and a Banach-valued holomorphic map `f : V → E` on a ball
`ball ζ r` in a complex normed space `V`, approximating the cell integral `∫ y in A, κ y • f y ∂μ`
over a finite-measure subset `A ⊆ ball ζ δ` (`δ ≤ r`) by the one-point value
`μ.real A • (κ ζ • f ζ)` incurs an error controlled by the oscillation of `κ` on `A` and the
supremum of `‖f‖` on `ball ζ r` (`TauCeti.norm_setIntegral_smul_sub_measureReal_smul_le`).

Summing this cell bound across a measurable small-ball partition turns integral representations of
holomorphic functions (such as the Cauchy or Cauchy–Pompeiu formulas) into uniform finite-rank
point-evaluation approximations, as in `TauCeti/Analysis/Complex/Runge/Operator.lean`.

## Main results

* `TauCeti.norm_setIntegral_smul_sub_measureReal_smul_le`: if `A ⊆ ball ζ δ` has finite measure
  with `δ ≤ r`, `‖κ y - κ ζ‖ ≤ ε` on `A`, and `f` is holomorphic and bounded in norm by `B` on
  `ball ζ r`, then
  `‖(∫ y in A, κ y • f y ∂μ) - μ.real A • (κ ζ • f ζ)‖ ≤ μ.real A * ((ε + 2 * ‖κ ζ‖ * δ / r) * B)`.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti

/-- **One-point quadrature error for a kernel-weighted holomorphic map.** If `A ⊆ ball ζ δ` has
finite measure with `δ ≤ r`, `κ` varies by at most `ε` from `κ ζ` on `A`, and `f` is holomorphic
and bounded in norm by `B` on `ball ζ r`, then replacing `∫ y in A, κ y • f y ∂μ` by
`μ.real A • (κ ζ • f ζ)` incurs error at most `μ.real A * ((ε + 2 * ‖κ ζ‖ * δ / r) * B)`. -/
theorem norm_setIntegral_smul_sub_measureReal_smul_le
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {μ : Measure V} {A : Set V} {κ : V → ℂ} {f : V → E} {ζ : V} {δ r ε B : ℝ}
    (hA : μ A < ∞) (hA_ball : A ⊆ ball ζ δ) (hδr : δ ≤ r)
    (hint : IntegrableOn (fun y ↦ κ y • f y) A μ)
    (hκ : ∀ y ∈ A, ‖κ y - κ ζ‖ ≤ ε)
    (hf : DifferentiableOn ℂ f (ball ζ r))
    (hfB : ∀ u ∈ ball ζ r, ‖f u‖ ≤ B) :
    ‖(∫ y in A, κ y • f y ∂μ) - μ.real A • (κ ζ • f ζ)‖ ≤
      μ.real A * ((ε + 2 * ‖κ ζ‖ * δ / r) * B) := by
  rw [← setIntegral_const, ← integral_sub hint (integrableOn_const hA.ne), mul_comm (μ.real A)]
  refine norm_setIntegral_le_of_norm_le_const hA fun y hy ↦ ?_
  have hy_δ : y ∈ ball ζ δ := hA_ball hy
  have hy_r : y ∈ ball ζ r := ball_subset_ball hδr hy_δ
  have hr : 0 < r := nonempty_ball.mp ⟨y, hy_r⟩
  have hfyB : ‖f y‖ ≤ B := hfB y hy_r
  have hB : 0 ≤ B := (norm_nonneg _).trans hfyB
  have hf_diff : ‖f y - f ζ‖ ≤ 2 * B / r * δ := by
    have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf
      (mapsTo_closedBall_of_forall_norm_le hfB (mem_ball_self hr)) hy_r
    rw [dist_eq_norm] at hsch
    exact hsch.trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy_δ).le (by positivity))
  have hsplit : κ y • f y - κ ζ • f ζ = (κ y - κ ζ) • f y + κ ζ • (f y - f ζ) := by
    rw [sub_smul, smul_sub, sub_add_sub_cancel]
  calc ‖κ y • f y - κ ζ • f ζ‖
      = ‖(κ y - κ ζ) • f y + κ ζ • (f y - f ζ)‖ := by rw [hsplit]
    _ ≤ ‖(κ y - κ ζ) • f y‖ + ‖κ ζ • (f y - f ζ)‖ := norm_add_le _ _
    _ = ‖κ y - κ ζ‖ * ‖f y‖ + ‖κ ζ‖ * ‖f y - f ζ‖ := by rw [norm_smul, norm_smul]
    _ ≤ ε * B + ‖κ ζ‖ * (2 * B / r * δ) :=
        add_le_add (mul_le_mul (hκ y hy) hfyB (norm_nonneg _) ((norm_nonneg _).trans (hκ y hy)))
          (mul_le_mul_of_nonneg_left hf_diff (norm_nonneg _))
    _ = (ε + 2 * ‖κ ζ‖ * δ / r) * B := by ring

end TauCeti
