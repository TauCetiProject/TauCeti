/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.Continuity

/-!
# Off-trace continuity of winding numbers for absolutely continuous curves

For an absolutely continuous curve, `windingNumber γ a b` is continuous at every point off its
trace `γ '' uIcc a b`. In particular, along symmetric linear perturbations `z ± h • u` about an
avoided point `z`, the difference of winding numbers tends to `0` as `h → 0`.
-/

public section

open Filter Set TauCeti.Contour
open scoped Topology

namespace AbsolutelyContinuousOnInterval

/-- The winding number of an absolutely continuous curve is continuous at every point off its
trace, in either orientation of the parameter interval. -/
theorem continuousAt_windingNumber {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hz : z ∉ γ '' uIcc a b) :
    ContinuousAt (windingNumber γ a b) z :=
  continuousAt_windingNumber_of_avoidance hγ.continuousOn
    (fun t ht heq ↦ hz ⟨t, ht, heq⟩) (hγ.intervalIntegrable_inv_sub_mul_deriv hz)

/-- At a point `z` off the trace of an absolutely continuous curve, the difference of its winding
numbers at symmetric perturbations `z ± h • u` tends to `0` as `h → 0`. -/
theorem tendsto_windingNumber_add_smul_sub {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hz : z ∉ γ '' uIcc a b) (u : ℂ) :
    Tendsto (fun h : ℝ ↦ windingNumber γ a b (z + h • u) - windingNumber γ a b (z - h • u))
      (𝓝 0) (𝓝 0) := by
  have hc := hγ.continuousAt_windingNumber hz
  simpa using (hc.tendsto.comp ((by fun_prop : Continuous fun h : ℝ ↦ z + h • u).tendsto' 0 z
      (by simp))).sub
    (hc.tendsto.comp ((by fun_prop : Continuous fun h : ℝ ↦ z - h • u).tendsto' 0 z (by simp)))

end AbsolutelyContinuousOnInterval
