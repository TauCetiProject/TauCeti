/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.DiskFunction
public import TauCeti.Analysis.Complex.Poisson.Basic
import TauCeti.MeasureTheory.Function.Lp.Integral.BoundedSmul

/-!
# The boundary Poisson formula for Hardy functions

The holomorphic disk function of a boundary Hardy function is its Poisson integral against
normalized Haar measure. The boundary function need only belong to `L²`; no continuous
boundary representative is assumed. This formula is the linear input to constructing a
harmonic majorant from the squared boundary modulus.

The proof applies the classical Poisson formula to radial dilations and passes to the
boundary using their `L²` convergence and boundedness of the kernel at each interior point.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Chapter 1, Poisson representation of Hardy functions.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Topology
open scoped ENNReal

namespace TauCeti.HardySpace

variable (x : HardySpace) {w : ℂ}

private theorem integral_poissonKernel_smul_radial {r : ℝ} (hr : |r| < 1)
    (hw : ‖w‖ < 1) :
    (∫ t : UnitAddCircle, poissonKernel 0 w (AddCircle.toCircle t) •
      x.diskFunction (r * AddCircle.toCircle t) ∂AddCircle.haarAddCircle) =
      x.diskFunction (r * w) := by
  have hmap : Set.MapsTo (fun z : ℂ ↦ (r : ℂ) * z)
      (Metric.closedBall 0 1) (Metric.ball 0 1) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    simpa [Metric.mem_ball, dist_eq_norm, norm_mul] using
      (mul_le_mul_of_nonneg_left hz' (abs_nonneg r)).trans_lt (by simpa using hr)
  have hf : DiffContOnCl ℂ (fun z : ℂ ↦ x.diskFunction (r * z)) (Metric.ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact x.differentiableOn_diskFunction.comp (by fun_prop) hmap
  have h := hf.circleAverage_poissonKernel_smul (by simpa using hw)
  rw [← AddCircle.integral_haarAddCircle_comp_toCircle (T := 1)
    (poissonKernel 0 w • fun z : ℂ ↦ x.diskFunction (r * z)) 0 1] at h
  simpa using h

/-- **The boundary Poisson formula.** The disk function of an arbitrary `L²` Hardy function
is its Poisson integral over the circle with normalized Haar measure. -/
theorem integral_poissonKernel_smul_eq_diskFunction (hw : ‖w‖ < 1) :
    (∫ t : UnitAddCircle, poissonKernel 0 w (AddCircle.toCircle t) •
      (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t ∂AddCircle.haarAddCircle) =
      x.diskFunction w := by
  let k : C(UnitAddCircle, ℝ) :=
    ⟨fun t ↦ poissonKernel 0 w (AddCircle.toCircle t), by
      apply (continuousOn_poissonKernel (s := Metric.sphere 0 1) (by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw.ne)).comp_continuous (by fun_prop)
      intro t
      simp⟩
  have hφ : ∀ᶠ r : ℝ in 𝓝[<] 1, MemLp
      (fun t : UnitAddCircle ↦ x.diskFunction (r * AddCircle.toCircle t)) 2
      AddCircle.haarAddCircle := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
    have hc : Continuous (fun t : UnitAddCircle ↦
        x.diskFunction (r * AddCircle.toCircle t)) := by
      apply x.analyticOnNhd_diskFunction.continuousOn.comp_continuous (by fun_prop)
      intro t
      simpa [Metric.mem_ball, dist_eq_norm, norm_mul] using abs_lt.mpr hr
    exact ContinuousMap.memLp AddCircle.haarAddCircle ℂ ⟨_, hc⟩
  have hlim := tendsto_integral_smul_of_tendsto_eLpNorm_sub
    (μ := AddCircle.haarAddCircle (T := 1)) (W := Set.univ) (k := k)
    (φ := fun r : ℝ ↦ fun t : UnitAddCircle ↦
      x.diskFunction (r * AddCircle.toCircle t))
    (f := (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
    (by simp) (norm_nonneg k)
    (by simpa using k.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ↦ k.norm_coe_le_norm t)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hφ
    (Lp.memLp (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
    (by simp) (by simp)
    x.tendsto_eLpNorm_diskFunction_sub
  have hpoint : Tendsto (fun r : ℝ ↦ x.diskFunction (r * w)) (𝓝[<] 1)
      (𝓝 (x.diskFunction w)) := by
    apply (x.analyticOnNhd_diskFunction.continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hw))).tendsto.comp
    simpa using ((Complex.continuous_ofReal.tendsto 1).mul_const w).mono_left
      nhdsWithin_le_nhds
  apply tendsto_nhds_unique hlim
  apply hpoint.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
  exact (x.integral_poissonKernel_smul_radial (abs_lt.mpr hr) hw).symm

end TauCeti.HardySpace
