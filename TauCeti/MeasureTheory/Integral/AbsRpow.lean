/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Positivity and derivative of the integral of `|u| ^ p`

For a continuous function `u ≠ 0` on a compact space with a finite measure that is positive on
nonempty open sets, the integral `∫ |u| ^ p dμ` is positive for every `p > 0`.

For `p > 1` the function `s ↦ |s| ^ p` is differentiable with derivative `p |s| ^ (p - 2) s`
(`hasDerivAt_abs_rpow`). This file differentiates the integral `t ↦ ∫ |u + t v| ^ p dμ` under the
integral sign, for continuous `u` and `v` on a compact space with a finite measure:

`d/dt ∫ |u + t v| ^ p dμ |_(t = 0) = p ∫ |u| ^ (p - 2) u v dμ`.

This is the directional derivative of the `p`-th power of the `Lᵖ` norm at `u` in the direction
`v`. It is the derivative of the denominator in the first variation of a Rayleigh-type quotient
`(∫ (energy of u) dμ) / (∫ |u| ^ p dμ) ^ (2 / p)`, such as the Yamabe quotient.

## Main declarations

* `TauCeti.integral_abs_rpow_pos`: positivity of `∫ |u| ^ p dμ` for a continuous `u ≠ 0`.
* `TauCeti.hasDerivAt_integral_abs_add_mul_rpow`: the derivative of `t ↦ ∫ |u + t v| ^ p dμ` at
  `t = 0`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The integral `∫ |u| ^ p dμ` of a continuous function `u ≠ 0` on a compact space is positive
for `p > 0`, when the finite measure `μ` is positive on nonempty open sets. -/
theorem integral_abs_rpow_pos [μ.IsOpenPosMeasure] {u : X → ℝ} (hu : Continuous u) (hu0 : u ≠ 0)
    {p : ℝ} (hp : 0 < p) :
    0 < ∫ x, |u x| ^ p ∂μ := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hu0
  exact (hu.abs.rpow_const fun _ ↦ Or.inr hp.le).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (HasCompactSupport.of_compactSpace _) (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (Real.rpow_pos_of_pos (abs_pos.2 hx) p).ne'

/-- **Differentiating `∫ |u + t v| ^ p dμ`.** For continuous `u` and `v` on a compact space with
a finite measure and `p > 1`, the derivative of `t ↦ ∫ |u + t v| ^ p dμ` at `t = 0` is
`p ∫ |u| ^ (p - 2) u v dμ`. -/
theorem hasDerivAt_integral_abs_add_mul_rpow {u v : X → ℝ} (hu : Continuous u)
    (hv : Continuous v) {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, |u x + t * v x| ^ p ∂μ)
      (p * ∫ x, |u x| ^ (p - 2) * u x * v x ∂μ) 0 := by
  have hint {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hlin (t : ℝ) : Continuous fun x ↦ u x + t * v x := hu.add (continuous_const.mul hv)
  have hcont (t : ℝ) : Continuous fun x ↦ |u x + t * v x| ^ p :=
    (hlin t).abs.rpow_const fun _ ↦ Or.inr (by linarith)
  have hderiv (x : X) (t : ℝ) : HasDerivAt (fun t ↦ |u x + t * v x| ^ p)
      (p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x)) t := by
    have := (hasDerivAt_abs_rpow (u x + t * v x) hp).comp t
      (((hasDerivAt_id t).mul_const (v x)).const_add (u x))
    simpa only [Function.comp_def, id, one_mul, mul_assoc] using this
  -- For `|t| < 1`, the derivative is bounded by `p (|u| + |v|) ^ (p - 1) |v|`.
  have hbound (x : X) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) :
      ‖p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x)‖ ≤
        p * ((|u x| + |v x|) ^ (p - 1) * |v x|) := by
    have htv : |t * v x| ≤ |v x| := by
      rw [abs_mul]
      have ht' : |t| ≤ 1 := by simpa using (Metric.mem_ball.1 ht).le
      nlinarith [abs_nonneg (v x), abs_nonneg t]
    have hy : |u x + t * v x| ≤ |u x| + |v x| := by linarith [abs_add_le (u x) (t * v x)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by linarith : 0 < p),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_add_one' (abs_nonneg _)
        (by linarith), show p - 2 + 1 = p - 1 by ring]
    gcongr
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F' := fun t x ↦ p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun t ↦ (hcont t).aestronglyMeasurable)
    (hint (hcont 0))
    (((((hlin 0).abs.measurable.pow_const (p - 2)).mul (hlin 0).measurable).mul
      hv.measurable).const_mul p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht ↦ hbound x t ht)
    (hint (continuous_const.mul
      (((hu.abs.add hv.abs).rpow_const fun _ ↦ Or.inr (by linarith)).mul hv.abs)))
    (Filter.Eventually.of_forall fun x t _ ↦ hderiv x t)
  simpa only [zero_mul, add_zero, integral_const_mul] using h.2

end TauCeti
