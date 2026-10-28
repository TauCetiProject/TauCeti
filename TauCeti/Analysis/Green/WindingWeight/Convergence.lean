/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.Bound
public import TauCeti.Analysis.Green.WindingWeight.FiniteSum
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
    (fun n ↦ (hγn n).aemeasurable_restrict_Ioc) hγ.aemeasurable_restrict_Ioc
    (fun n ↦ (hγn n).integrableOn_deriv_Ioc) hγ.integrableOn_deriv_Ioc hμconv hderiv'
  have hbound := hpot.const_mul ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖
  apply squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) ?_
    (by simpa only [mul_zero] using hbound)
  filter_upwards [hγnR] with n hn
  simpa only [Real.norm_eq_abs] using
    integral_norm_windingWeight_sub_le_cauchyPotential hab hγ (hγn n) hγclosed
      (hγnclosed n) hγR hn

section

variable {ι : Type*} {s : Finset ι} {γ : ι → ℝ → ℂ} {γn : ℕ → ι → ℝ → ℂ}
  {a b : ι → ℝ} {w : ι → ℤ}

/-- Per-curve uniform and derivative `L¹` convergence imply `L¹` convergence of the actual total
real winding weight. No uniform bound on the indices is assumed. -/
theorem tendsto_integral_abs_sum_windingWeight_sub
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hγn : ∀ n, ∀ i ∈ s, AbsolutelyContinuousOnInterval (γn n i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i))
    (hclosedn : ∀ n, ∀ i ∈ s, γn n i (a i) = γn n i (b i))
    (hconv : ∀ i ∈ s, TendstoUniformlyOn (fun n ↦ γn n i) (γ i) atTop (Icc (a i) (b i)))
    (hdconv : ∀ i ∈ s, Tendsto
      (fun n ↦ ∫ t in a i..b i, ‖deriv (γn n i) t - deriv (γ i) t‖) atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ z : ℂ,
      |(∑ i ∈ s, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z) -
        ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z|) atTop (nhds 0) := by
  have hd (n : ℕ) (i : ι) (hi : i ∈ s) :
      Integrable (fun z ↦ |windingWeight (γn n i) (a i) (b i) z -
        windingWeight (γ i) (a i) (b i) z|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((AbsolutelyContinuousOnInterval.integrable_windingWeight (hγn n i hi) (hclosedn n i hi)).sub
        (AbsolutelyContinuousOnInterval.integrable_windingWeight (hγ i hi) (hclosed i hi))).norm
  have hlim : Tendsto
      (fun n ↦ ∑ i ∈ s, |(w i : ℝ)| *
        ∫ z : ℂ, |windingWeight (γn n i) (a i) (b i) z - windingWeight (γ i) (a i) (b i) z|)
      atTop (nhds 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using tendsto_finsetSum s (fun i hi ↦
      Tendsto.const_mul |(w i : ℝ)|
        (tendsto_integral_abs_windingWeight_sub (hab i hi) (fun n ↦ hγn n i hi)
          (hγ i hi) (fun n ↦ hclosedn n i hi) (hclosed i hi) (hconv i hi) (hdconv i hi)))
  apply squeeze_zero (fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) (fun n ↦ ?_) hlim
  have htotal : Integrable (fun z ↦
      |(∑ i ∈ s, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z) -
        ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((integrable_sum_windingWeight (fun i hi ↦ hγn n i hi) (fun i hi ↦ hclosedn n i hi)).sub
        (integrable_sum_windingWeight hγ hclosed)).norm
  calc
    _ ≤ ∫ z : ℂ, ∑ i ∈ s, |(w i : ℝ)| *
        |windingWeight (γn n i) (a i) (b i) z - windingWeight (γ i) (a i) (b i) z| := by
      apply integral_mono htotal (integrable_finsetSum _ fun i hi ↦ (hd n i hi).const_mul _)
      intro z
      dsimp only
      rw [← Finset.sum_sub_distrib]
      have heq : ∀ i, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z -
          (w i : ℝ) * windingWeight (γ i) (a i) (b i) z =
          (w i : ℝ) * (windingWeight (γn n i) (a i) (b i) z -
            windingWeight (γ i) (a i) (b i) z) := fun i ↦ (mul_sub _ _ _).symm
      simp_rw [heq]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (f := fun i ↦ (w i : ℝ) * (windingWeight (γn n i) (a i) (b i) z -
          windingWeight (γ i) (a i) (b i) z)) s
    _ = _ := by
      rw [integral_finsetSum s (fun i hi ↦ (hd n i hi).const_mul _)]
      simp only [integral_const_mul]

end

end TauCeti.Green
