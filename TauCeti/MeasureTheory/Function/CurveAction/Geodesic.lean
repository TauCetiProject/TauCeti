/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.Topology.MetricSpace.Length

/-!
# The action of a geodesic segment

A constant-speed geodesic has constant metric derivative on the interior of its parameter
interval. Consequently its `p`-action is exactly the `p`th power of the distance between its
endpoints. This is the pathwise identity used when dynamic plans are concentrated on minimizing
geodesics.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Interval

namespace TauCeti

variable {X : Type*} [MetricSpace X] {γ : ℝ → X} {x y : X}

/-- On the interior of its parameter interval, a constant-speed geodesic segment has metric
derivative equal to the distance between its endpoints. -/
theorem IsGeodesicSegment.metricDerivative_eq (h : IsGeodesicSegment γ x y)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    metricDerivative γ t = ENNReal.ofReal (dist x y) := by
  apply metricDerivative_eq_of_tendsto
  have hIoo : ∀ᶠ s in 𝓝[≠] t, s ∈ Ioo (0 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2)
  have hquot : (fun s ↦ edist (γ s) (γ t) / edist s t) =ᶠ[𝓝[≠] t]
      fun _ ↦ ENNReal.ofReal (dist x y) := by
    filter_upwards [hIoo, self_mem_nhdsWithin] with s hs hst
    have hst' : s ≠ t := by simpa using hst
    rw [edist_dist, edist_dist, h.dist_eq s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩,
      Real.dist_eq]
    rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
    exact ENNReal.mul_div_cancel_right
      (ENNReal.ofReal_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hst'))).ne'
      ENNReal.ofReal_ne_top
  exact tendsto_const_nhds.congr' hquot.symm

/-- The `p`-action of a constant-speed geodesic segment is the `p`th power of the distance
between its endpoints. The values of the metric derivative at the two endpoints do not affect the
integral. -/
theorem IsGeodesicSegment.curveAction_eq (h : IsGeodesicSegment γ x y) (p : ℝ) :
    curveAction p γ 0 1 = ENNReal.ofReal (dist x y) ^ p := by
  rw [curveAction_def]
  have hderiv : (fun t ↦ metricDerivative γ t ^ p) =ᵐ[volume.restrict (Ι (0 : ℝ) 1)]
      fun _ ↦ ENNReal.ofReal (dist x y) ^ p := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
    filter_upwards [volume.ae_ne 1] with t h1 ht
    rw [uIoc_of_le zero_le_one] at ht
    exact congrArg (fun z : ℝ≥0∞ ↦ z ^ p)
      (h.metricDerivative_eq ⟨ht.1, lt_of_le_of_ne ht.2 h1⟩)
  rw [lintegral_congr_ae hderiv, setLIntegral_const, Real.volume_uIoc]
  simp

end TauCeti
