/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Derivative of the integral of `exp (u + t v)`

For continuous functions `u` and `v` on a compact space with a finite measure, this file
differentiates `t ↦ ∫ exp (u + t v) dμ` under the integral sign:

`d/dt ∫ exp (u + t v) dμ = ∫ v exp (u + t v) dμ`.

This is the directional derivative of the exponential integral `∫ e^u dμ` at `u` in the direction
`v`, the derivative of the exponential term in Liouville-type energies such as
`TauCeti.Manifold.liouvilleEnergy`.

## Main declarations

* `TauCeti.hasDerivAt_integral_exp_add_mul`: the derivative of `t ↦ ∫ exp (u + t v) dμ`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- **Differentiating `∫ exp (u + t v) dμ`.** For continuous `u` and `v` on a compact space with a
finite measure, the derivative of `t ↦ ∫ exp (u + t v) dμ` at `t₀` is
`∫ v exp (u + t₀ v) dμ`. -/
theorem hasDerivAt_integral_exp_add_mul {u v : X → ℝ} (hu : Continuous u) (hv : Continuous v)
    (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, Real.exp (u x + t * v x) ∂μ)
      (∫ x, v x * Real.exp (u x + t₀ * v x) ∂μ) t₀ := by
  have hint {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (.of_compactSpace f)
  have hF (t : ℝ) : Continuous fun x ↦ Real.exp (u x + t * v x) := by fun_prop
  -- On `|t - t₀| < 1` the `t`-derivative `v e^(u + t v)` is at most `|v| e^(|u| + (|t₀| + 1) |v|)`.
  have hbound (x : X) (t : ℝ) (ht : t ∈ Metric.ball t₀ 1) :
      ‖v x * Real.exp (u x + t * v x)‖ ≤ |v x| * Real.exp (|u x| + (|t₀| + 1) * |v x|) := by
    have ht' : |t| ≤ |t₀| + 1 := by
      have := (Real.dist_eq t t₀ ▸ Metric.mem_ball.1 ht).le
      calc |t| = |t₀ + (t - t₀)| := by rw [add_sub_cancel]
        _ ≤ |t₀| + |t - t₀| := abs_add_le _ _
        _ ≤ |t₀| + 1 := by gcongr
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (add_le_add (le_abs_self _) ?_))
      (abs_nonneg _)
    calc t * v x ≤ |t| * |v x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (|t₀| + 1) * |v x| := by gcongr
  have hderiv (x : X) (t : ℝ) :
      HasDerivAt (fun t ↦ Real.exp (u x + t * v x)) (v x * Real.exp (u x + t * v x)) t := by
    have := (((hasDerivAt_id' t).mul_const (v x)).const_add (u x)).exp
    convert this using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F' := fun t x ↦ v x * Real.exp (u x + t * v x))
    (bound := fun x ↦ |v x| * Real.exp (|u x| + (|t₀| + 1) * |v x|))
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t ↦ (hF t).aestronglyMeasurable)
    (hint (hF t₀)) (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun x t ht ↦ hbound x t ht) (hint (by fun_prop))
    (ae_of_all _ fun x t _ ↦ hderiv x t)).2

end TauCeti
