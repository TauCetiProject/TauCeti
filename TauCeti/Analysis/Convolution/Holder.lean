/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrable kernels preserve bounded Hölder estimates

Convolution with an integrable scalar kernel preserves both a uniform bound and a Hölder
constant, multiplying each by the integral of the kernel norm. This applies to truncated planar
Cauchy and Newtonian kernels, and to the normalized smoothing kernels used to pass their
estimates from smooth to Hölder data.
-/

public noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

namespace TauCeti

variable {E 𝕜 F : Type*} [NormedAddCommGroup E] [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F]
  {K : E → 𝕜} {f : E → F} {M : ℝ}

omit [NormedSpace ℝ F] in
/-- A kernel cutoff at the sum of the support and output radii leaves its convolution
integrand unchanged on the output disc. -/
theorem indicator_kernel_smul_sub_eq {c w : E} {r R : ℝ}
    (hs : Function.support f ⊆ closedBall c r) (hw : w ∈ closedBall c R) (z : E) :
    (closedBall 0 (r + R)).indicator K z • f (w - z) = K z • f (w - z) := by
  by_cases hz : z ∈ closedBall 0 (r + R)
  · rw [indicator_of_mem hz]
  · have hf : f (w - z) = 0 := by
      apply Function.notMem_support.mp
      intro hf
      have hz' : ‖z‖ ≤ r + R := by
        calc
          ‖z‖ = dist w (w - z) := by simp
          _ ≤ dist w c + dist c (w - z) := dist_triangle _ _ _
          _ ≤ R + r := add_le_add (mem_closedBall.mp hw)
            (by simpa only [dist_comm] using mem_closedBall.mp (hs hf))
          _ = r + R := by ring
      exact hz (mem_closedBall_zero_iff.mpr hz')
    simp only [hf, smul_zero]

variable [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopologyEither E F] {μ : Measure E}

omit [NormedSpace ℝ F] in
/-- A bounded continuous function is integrable against every translate of an integrable
scalar kernel. -/
theorem integrable_kernel_smul_sub (hK : Integrable K μ) (hf : Continuous f)
    (hM : ∀ x, ‖f x‖ ≤ M) (w : E) : Integrable (fun z ↦ K z • f (w - z)) μ := by
  apply (hK.norm.mul_const M).mono'
  · exact hK.aestronglyMeasurable.smul
      ((hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact ae_of_all _ fun z ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

omit [OpensMeasurableSpace E] [SecondCountableTopologyEither E F] in
/-- An integrable scalar kernel multiplies the uniform bound by its `L¹` norm. -/
theorem norm_integral_kernel_smul_sub_le (hK : Integrable K μ)
    (hM : ∀ x, ‖f x‖ ≤ M) (w : E) :
    ‖∫ z, K z • f (w - z) ∂μ‖ ≤ (∫ z, ‖K z‖ ∂μ) * M := by
  calc
    _ ≤ ∫ z : E, ‖K z‖ * M ∂μ := norm_integral_le_of_norm_le (hK.norm.mul_const M)
      (ae_of_all _ fun z ↦ by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
    _ = _ := integral_mul_const _ _

/-- **A kernel of integral zero converts Hölder continuity into decay.** If `∫ K = 0`, the
convolution integral `∫ K z • f (w - z)` of an `α`-Hölder function with constant `H` is at most
`H` times the `α`-th moment `∫ ‖z‖ ^ α ‖K z‖` of the kernel. No boundedness of `f` is needed. -/
theorem norm_integral_kernel_smul_sub_le_of_integral_eq_zero (hK : Integrable K μ)
    (hK0 : ∫ z, K z ∂μ = 0) {H α : ℝ≥0} (hKα : Integrable (fun z ↦ ‖z‖ ^ (α : ℝ) * ‖K z‖) μ)
    (hf : HolderWith H α f) (hfc : Continuous f) (w : E) :
    ‖∫ z, K z • f (w - z) ∂μ‖ ≤ H * ∫ z, ‖z‖ ^ (α : ℝ) * ‖K z‖ ∂μ := by
  have hbound : ∀ z, ‖K z • (f (w - z) - f w)‖ ≤ H * (‖z‖ ^ (α : ℝ) * ‖K z‖) := fun z ↦ by
    rw [norm_smul, ← dist_eq_norm, mul_comm]
    calc dist (f (w - z)) (f w) * ‖K z‖ ≤ (H * ‖z‖ ^ (α : ℝ)) * ‖K z‖ := by
          gcongr
          simpa using hf.dist_le (w - z) w
      _ = H * (‖z‖ ^ (α : ℝ) * ‖K z‖) := mul_assoc _ _ _
  have hint : Integrable (fun z ↦ K z • (f (w - z) - f w)) μ :=
    (hKα.const_mul H).mono'
      (hK.aestronglyMeasurable.smul
        ((hfc.comp (continuous_const.sub continuous_id)).sub continuous_const).aestronglyMeasurable)
      (ae_of_all _ hbound)
  -- Subtracting the constant `f w` costs nothing, since `K` has integral zero.
  have hsub : ∫ z, K z • f (w - z) ∂μ = ∫ z, K z • (f (w - z) - f w) ∂μ := by
    by_cases hF : CompleteSpace F
    · have h := integral_add hint (hK.smul_const (f w))
      simp only [← smul_add, sub_add_cancel] at h
      rw [h, integral_smul_const, hK0, zero_smul, add_zero]
    · simp only [integral_of_not_completeSpace hF]
  rw [hsub, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hKα.const_mul H) (ae_of_all _ hbound)

/-- An integrable scalar kernel preserves a Hölder exponent and multiplies its constant by
its `L¹` norm. No boundedness is needed: the Hölder condition makes any two translates of the
integrand differ by an integrable function, so either every convolution integral is
well-defined or none is, and then all of them vanish. -/
theorem holderWith_integral_kernel_smul_sub (hK : Integrable K μ)
    {H α : ℝ≥0} (hα : 0 < α) (hf : HolderWith H α f) :
    HolderWith ((∫ z, ‖K z‖ ∂μ).toNNReal * H) α (fun w ↦ ∫ z, K z • f (w - z) ∂μ) := by
  rw [← holderOnWith_univ]
  apply HolderOnWith.of_dist_le
  intro w _ v _
  have hmeas (x : E) : AEStronglyMeasurable (fun z ↦ K z • f (x - z)) μ :=
    hK.aestronglyMeasurable.smul
      ((hf.continuous hα).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbound (z : E) : ‖K z • f (w - z) - K z • f (v - z)‖ ≤ ‖K z‖ * (H * dist w v ^ (α : ℝ)) := by
    rw [← smul_sub, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [dist_sub_right, dist_eq_norm, sub_sub_sub_cancel_right] using
      hf.dist_le (w - z) (v - z)
  have hdiff : Integrable (fun z ↦ K z • f (w - z) - K z • f (v - z)) μ :=
    (hK.norm.mul_const _).mono' ((hmeas w).sub (hmeas v)) (ae_of_all _ hbound)
  by_cases hw : Integrable (fun z ↦ K z • f (w - z)) μ
  · have hv : Integrable (fun z ↦ K z • f (v - z)) μ :=
      (hw.sub hdiff).congr (ae_of_all _ fun z ↦ by simp)
    rw [dist_eq_norm, ← integral_sub hw hv]
    calc
      _ ≤ ∫ z : E, ‖K z‖ * (H * dist w v ^ (α : ℝ)) ∂μ :=
        norm_integral_le_of_norm_le (hK.norm.mul_const _) (ae_of_all _ hbound)
      _ = _ := by
        rw [integral_mul_const, NNReal.coe_mul,
          Real.coe_toNNReal _ (integral_nonneg fun z ↦ norm_nonneg (K z))]
        ring
  · have hv : ¬ Integrable (fun z ↦ K z • f (v - z)) μ := fun hv ↦
      hw ((hv.add hdiff).congr (ae_of_all _ fun z ↦ by simp))
    rw [integral_undef hw, integral_undef hv, dist_self]
    positivity

end TauCeti
