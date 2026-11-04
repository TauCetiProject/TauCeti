/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.DiskFunction
public import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Radial means and harmonic majorants of Hardy functions

Using the convergence of squared radial means to the squared boundary norm from
`DiskFunction`, every real harmonic majorant of the squared disk modulus has value at the
origin at least this boundary norm squared. This is the lower bound needed to identify the
boundary norm with the norm defined by harmonic majorants.

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
