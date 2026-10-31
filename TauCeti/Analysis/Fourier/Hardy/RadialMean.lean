/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.DiskFunction
public import TauCeti.MeasureTheory.Integral.Circle.Haar
public import TauCeti.MeasureTheory.Function.Lp.Norm
public import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Radial means and harmonic majorants of Hardy functions

The squared radial means of a boundary Hardy function's disk function tend to its squared
boundary norm. Consequently every real harmonic majorant of the squared modulus has value
at the origin at least this boundary norm squared. This is the lower bound needed to identify
the boundary norm with the norm defined by harmonic majorants.

The circle means here are Mathlib's `Real.circleAverage`; the boundary norm uses normalized
Haar measure on `UnitAddCircle`. The comparison uses the Haar-to-circle-average transport and
the radial `L²` convergence of `HardySpace.diskFunction`.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Chapter 1, the harmonic-majorant characterization of H².
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped InnerProductSpace

namespace TauCeti.HardySpace

variable (x : HardySpace)

private theorem continuous_radial_diskFunction {r : ℝ} (hr : |r| < 1) :
    Continuous (fun t : UnitAddCircle ↦ x.diskFunction (r * AddCircle.toCircle t)) := by
  apply x.analyticOnNhd_diskFunction.continuousOn.comp_continuous
  · fun_prop
  · intro t
    simpa [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real] using hr

/-- The squared circle means of the disk function converge to the squared boundary Hardy norm
as the radius tends to one from below. -/
theorem tendsto_circleAverage_norm_sq_diskFunction :
    Tendsto (fun r : ℝ ↦ Real.circleAverage (fun w ↦ ‖x.diskFunction w‖ ^ 2) 0 r)
      (𝓝[<] 1) (𝓝 (‖x‖ ^ 2)) := by
  -- Use continuous representatives on interior circles, and zero elsewhere; the latter values
  -- do not affect the one-sided limit.
  let f (r : ℝ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    if hr : |r| < 1 then
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        ⟨_, x.continuous_radial_diskFunction hr⟩
    else 0
  have hcoe {r : ℝ} (hr : |r| < 1) :
      f r =ᵐ[AddCircle.haarAddCircle]
        fun t ↦ x.diskFunction (r * AddCircle.toCircle t) := by
    simp only [f, dite_eq_left hr]
    exact ContinuousMap.coeFn_toLp _ _
  have hev : ∀ᶠ r : ℝ in 𝓝[<] 1, |r| < 1 :=
    eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1))
      fun _ hr ↦ abs_lt.mpr hr
  have hlim : Tendsto f (𝓝[<] 1)
      (𝓝 (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    refine x.tendsto_eLpNorm_diskFunction_sub.congr' ?_
    filter_upwards [hev] with r hr
    exact eLpNorm_congr_ae ((hcoe hr).symm.sub (Filter.EventuallyEq.rfl))
  have hsq := hlim.norm.pow 2
  refine hsq.congr' ?_
  filter_upwards [hev] with r hr
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc
    (∫ t, ‖f r t‖ ^ 2 ∂AddCircle.haarAddCircle) =
        ∫ t : UnitAddCircle, ‖x.diskFunction (r * AddCircle.toCircle t)‖ ^ 2
          ∂AddCircle.haarAddCircle :=
      integral_congr_ae ((hcoe hr).fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
    _ = Real.circleAverage (fun w ↦ ‖x.diskFunction w‖ ^ 2) 0 r := by
      simpa only [add_zero] using AddCircle.integral_haarAddCircle_comp_toCircle
        (T := 1) (fun w ↦ ‖x.diskFunction w‖ ^ 2) 0 r

/-- A harmonic majorant of the squared disk modulus bounds each interior squared circle mean
by its value at the origin. No boundary regularity of the majorant is required. -/
theorem circleAverage_norm_sq_diskFunction_le_of_harmonic_majorant
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (Metric.ball 0 1))
    (hmajor : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖x.diskFunction w‖ ^ 2 ≤ u w)
    {r : ℝ} (hr : |r| < 1) :
    Real.circleAverage (fun w ↦ ‖x.diskFunction w‖ ^ 2) 0 r ≤ u 0 := by
  have hsub : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball hr
  have hus := hu.mono hsub
  rw [← hus.circleAverage_eq (R := r)]
  apply Real.circleAverage_mono
  · exact ((x.analyticOnNhd_diskFunction.continuousOn.mono
      (Metric.sphere_subset_closedBall.trans hsub)).norm.pow 2).circleIntegrable'
  · exact (hus.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable'
  · intro w hw
    exact hmajor w (hsub (Metric.sphere_subset_closedBall hw))

/-- Every real harmonic majorant of the squared disk modulus has value at the origin at least
the squared boundary Hardy norm. -/
theorem norm_sq_le_harmonic_majorant_zero
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (Metric.ball 0 1))
    (hmajor : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖x.diskFunction w‖ ^ 2 ≤ u w) :
    ‖x‖ ^ 2 ≤ u 0 := by
  apply le_of_tendsto x.tendsto_circleAverage_norm_sq_diskFunction
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
  exact x.circleAverage_norm_sq_diskFunction_le_of_harmonic_majorant hu hmajor (abs_lt.mpr hr)

end TauCeti.HardySpace
