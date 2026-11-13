/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MetricDerivative.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Affine

/-!
# Affine reparameterization of metric curves

An affine change of time multiplies the metric derivative by the absolute value of its slope.
This pointwise chain rule uses the upper-limit definition of speed, so it requires neither
differentiability nor absolute continuity of the curve. For nonzero slope, the integral of the
`p`-th power of speed scales by the absolute slope to the power `p - 1`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 1.
-/

public section

open Filter Topology MeasureTheory Set
open scoped ENNReal Interval

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X]

/-- An affine change of time multiplies speed by the absolute value of its slope.
The equality holds at every time, even when the metric derivative is infinite. A zero slope
gives a constant curve, of speed zero. -/
theorem metricDerivative_comp_mul_add (γ : ℝ → X) (c d t : ℝ) :
    metricDerivative (fun s ↦ γ (c * s + d)) t =
      ENNReal.ofReal |c| * metricDerivative γ (c * t + d) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [metricDerivative_def]
  have hdist (s : ℝ) : edist (c * s + d) (c * t + d) =
      ENNReal.ofReal |c| * edist s t := by
    simp only [edist_dist, Real.dist_eq]
    have hsub : c * s + d - (c * t + d) = c * (s - t) := by ring
    rw [hsub, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  have hq (s : ℝ) : edist (γ (c * s + d)) (γ (c * t + d)) / edist s t =
      ENNReal.ofReal |c| *
        (edist (γ (c * s + d)) (γ (c * t + d)) / edist (c * s + d) (c * t + d)) := by
    have h0 : ENNReal.ofReal |c| ≠ 0 := by simpa using hc
    rw [hdist, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top]
  have hmap := (affineHomeomorph c d hc).map_punctured_nhds_eq t
  simp only [affineHomeomorph_apply] at hmap
  rw [metricDerivative_def, metricDerivative_def, ← ENNReal.limsup_const_mul_of_ne_top
    ENNReal.ofReal_ne_top, ← hmap, ← limsup_comp]
  simp only [Function.comp_def, affineHomeomorph_apply]
  exact congrArg (fun f : ℝ → ℝ≥0∞ ↦ limsup f (𝓝[≠] t)) (funext hq)

/-- An invertible affine change of time scales the integral of the `p`-th power of speed
by `|c| ^ (p - 1)`. This holds for every real exponent, without measurability or finiteness
assumptions on the curve. -/
theorem setLIntegral_metricDerivative_comp_mul_add_rpow (p : ℝ) (γ : ℝ → X)
    {c : ℝ} (hc : c ≠ 0) (d a b : ℝ) :
    ∫⁻ t in Ι a b, metricDerivative (fun t ↦ γ (c * t + d)) t ^ p =
      ENNReal.ofReal |c| ^ (p - 1) *
        ∫⁻ t in Ι (c * a + d) (c * b + d), metricDerivative γ t ^ p := by
  have h0 : ENNReal.ofReal |c| ≠ 0 := by simpa using hc
  have hscale : ENNReal.ofReal |c| ^ p * ENNReal.ofReal |c⁻¹| =
      ENNReal.ofReal |c| ^ (p - 1) := by
    simp [abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.2 hc),
      ENNReal.rpow_sub p 1 h0 ENNReal.ofReal_ne_top, div_eq_mul_inv]
  have hpow (t : ℝ) : (ENNReal.ofReal |c| * metricDerivative γ (c * t + d)) ^ p =
      ENNReal.ofReal |c| ^ p * metricDerivative γ (c * t + d) ^ p := by
    simp [ENNReal.mul_rpow_eq_ite, h0]
  simp_rw [metricDerivative_comp_mul_add γ c, hpow]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero h0 ENNReal.ofReal_ne_top)]
  rw [setLIntegral_comp_mul_add_uIoc (fun t ↦ metricDerivative γ t ^ p) hc d a b]
  rw [← mul_assoc, hscale]

end TauCeti
