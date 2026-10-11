/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MetricDerivative.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Affine reparameterization of metric derivatives

An affine change of time multiplies the metric derivative by the absolute value of its slope.
This pointwise chain rule uses the upper-limit definition of speed, so it requires neither
differentiability nor absolute continuity of the curve.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 1.
-/

public section

open Filter Topology
open scoped ENNReal

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
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addRight d)
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
  have he (s : ℝ) : e s = c * s + d := rfl
  have hmap := e.map_punctured_nhds_eq t
  rw [he] at hmap
  rw [metricDerivative_def, metricDerivative_def, ← ENNReal.limsup_const_mul_of_ne_top
    ENNReal.ofReal_ne_top, ← hmap, ← limsup_comp]
  exact congrArg (fun f : ℝ → ℝ≥0∞ ↦ limsup f (𝓝[≠] t)) (funext hq)

end TauCeti
