/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.Bound
public import Mathlib.Topology.UniformSpace.UniformConvergence
import TauCeti.MeasureTheory.Integral.KernelPotential
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# `L¹` convergence of winding weights

Uniform convergence of closed absolutely continuous curves, together with `L¹` convergence of
their derivatives, gives global `L¹` convergence of their winding weights. The estimate uses
translation continuity of a compactly truncated complex reciprocal kernel.
-/

public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace TauCeti.Green

variable {γ δ : ℝ → ℂ} {a b R : ℝ}

/-- Uniform convergence of closed absolutely continuous curves and `L¹` convergence of their
derivatives imply global `L¹` convergence of their winding weights. -/
theorem tendsto_integral_abs_windingWeight_sub {γn : ℕ → ℝ → ℂ} (hab : a ≤ b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγnclosed : ∀ n, γn n a = γn n b) (hγclosed : γ a = γ b)
    (hconv : TendstoUniformlyOn γn γ atTop (Icc a b))
    (hderiv : Tendsto (fun n ↦ ∫ t in a..b, ‖deriv (γn n) t - deriv γ t‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z : ℂ, |windingWeight (γn n) a b z - windingWeight γ a b z|)
      atTop (𝓝 0) := by
  obtain ⟨S, -, hS⟩ := (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isBounded
    |>.exists_pos_norm_lt
  let R := S + 1
  have hγR : ∀ t ∈ uIcc a b, γ t ∈ closedBall 0 R := fun t ht ↦
    mem_closedBall_zero_iff.mpr (by dsimp [R]; linarith [hS (γ t) ⟨t, ht, rfl⟩])
  have hγnR : ∀ᶠ n in atTop, ∀ t ∈ uIcc a b, γn n t ∈ closedBall 0 R := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv 1 zero_lt_one] with n hn
    intro t ht
    have hdist := hn t ((uIcc_of_le hab) ▸ ht)
    apply mem_closedBall_zero_iff.mpr
    have hnorm : ‖γn n t‖ ≤ ‖γ t‖ + 1 :=
      norm_le_norm_add_const_of_dist_le (by simpa only [dist_comm] using hdist.le)
    dsimp [R]
    linarith [hS (γ t) ⟨t, ht, rfl⟩]
  have hμconv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Tendsto (fun n ↦ γn n t) atTop (𝓝 (γ t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hconv.tendsto_at (Ioc_subset_Icc_self ht)
  have hderiv' : Tendsto
      (fun n ↦ ∫ t in Ioc a b, ‖deriv (γn n) t - deriv γ t‖) atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le hab] using hderiv
  have hpot := (integrable_truncatedCauchyKernel (2 * R)).tendsto_integral_norm_kernel_potential_sub
    (measurable_truncatedCauchyKernel (2 * R))
    (fun n ↦ (hγn n).aemeasurable_restrict_Ioc hab) (hγ.aemeasurable_restrict_Ioc hab)
    (fun n ↦ (hγn n).integrableOn_deriv_Ioc hab) (hγ.integrableOn_deriv_Ioc hab) hμconv hderiv'
  have hbound := hpot.const_mul ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖
  apply squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) ?_
    (by simpa only [mul_zero] using hbound)
  filter_upwards [hγnR] with n hn
  simpa only [Real.norm_eq_abs] using
    integral_norm_windingWeight_sub_le_cauchyPotential hab hγ (hγn n) hγclosed
      (hγnclosed n) hγR hn

end TauCeti.Green
