/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivative of the integral of `exp (u + t v)`

For measurable functions `u` and `v` such that `exp (u + s v)` is integrable for every real `s`,
this file differentiates `t ↦ ∫ exp (u + t v) dμ` under the integral sign:

`d/dt ∫ exp (u + t v) dμ = ∫ v exp (u + t v) dμ`.

This is the directional derivative of the exponential integral `∫ e^u dμ` at `u` in the direction
`v`, the derivative of the exponential term in Liouville-type energies such as
`TauCeti.Manifold.liouvilleEnergy`. The integrability hypothesis holds for continuous `u` and `v`
on a compact space with a finite measure, and, by Trudinger's inequality, for the values of
`H¹` functions on a closed surface.

## Main declarations

* `TauCeti.hasDerivAt_integral_exp_add_mul`: the derivative of `t ↦ ∫ exp (u + t v) dμ`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Differentiating `∫ exp (u + t v) dμ`.** Let `v` be almost everywhere strongly measurable,
and let `exp (u + s v)` be integrable for every real `s`. Then the derivative of
`t ↦ ∫ exp (u + t v) dμ` at `t₀` is `∫ v exp (u + t₀ v) dμ`. -/
theorem hasDerivAt_integral_exp_add_mul {u v : X → ℝ} (hv : AEStronglyMeasurable v μ)
    (hint : ∀ s : ℝ, Integrable (fun x ↦ Real.exp (u x + s * v x)) μ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, Real.exp (u x + t * v x) ∂μ)
      (∫ x, v x * Real.exp (u x + t₀ * v x) ∂μ) t₀ := by
  -- On `|t - t₀| < 1`, the bound `|v| ≤ exp |v|` gives `|v e^(u + t v)| ≤ e^(u + t₀ v + 2 |v|)`,
  -- which is at most `e^(u + (t₀ + 2) v) + e^(u + (t₀ - 2) v)`.
  have hbound (x : X) (t : ℝ) (ht : t ∈ Metric.ball t₀ 1) :
      ‖v x * Real.exp (u x + t * v x)‖ ≤
        Real.exp (u x + (t₀ + 2) * v x) + Real.exp (u x + (t₀ - 2) * v x) := by
    have ht' : |t - t₀| ≤ 1 := (Real.dist_eq t t₀ ▸ Metric.mem_ball.1 ht).le
    have hv1 : |v x| ≤ Real.exp |v x| := by linarith [Real.add_one_le_exp |v x|]
    have htv : t * v x ≤ t₀ * v x + |v x| := by
      have : (t - t₀) * v x ≤ |v x| := by
        calc (t - t₀) * v x ≤ |(t - t₀) * v x| := le_abs_self _
          _ = |t - t₀| * |v x| := abs_mul _ _
          _ ≤ 1 * |v x| := by gcongr
          _ = |v x| := one_mul _
      linarith
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc |v x| * Real.exp (u x + t * v x)
        ≤ Real.exp |v x| * Real.exp (u x + t * v x) := by gcongr
      _ = Real.exp (u x + t * v x + |v x|) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (u x + t₀ * v x + 2 * |v x|) := Real.exp_le_exp.2 (by linarith)
      _ ≤ _ := by
        rcases le_total 0 (v x) with h | h
        · rw [abs_of_nonneg h, show u x + t₀ * v x + 2 * v x = u x + (t₀ + 2) * v x by ring]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_nonpos h, show u x + t₀ * v x + 2 * -v x = u x + (t₀ - 2) * v x by ring]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hderiv (x : X) (t : ℝ) :
      HasDerivAt (fun t ↦ Real.exp (u x + t * v x)) (v x * Real.exp (u x + t * v x)) t := by
    have := (((hasDerivAt_id' t).mul_const (v x)).const_add (u x)).exp
    convert this using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F' := fun t x ↦ v x * Real.exp (u x + t * v x))
    (bound := fun x ↦ Real.exp (u x + (t₀ + 2) * v x) + Real.exp (u x + (t₀ - 2) * v x))
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t ↦ (hint t).aestronglyMeasurable)
    (hint t₀) (hv.mul (hint t₀).aestronglyMeasurable)
    (ae_of_all _ fun x t ht ↦ hbound x t ht) ((hint _).add (hint _))
    (ae_of_all _ fun x t _ ↦ hderiv x t)).2

end TauCeti
