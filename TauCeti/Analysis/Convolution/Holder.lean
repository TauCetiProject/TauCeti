/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.MetricSpace.Holder
public import Mathlib.Algebra.Group.EvenFunction
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrable kernels preserve bounded Hölder estimates

Convolution with an integrable scalar kernel preserves both a uniform bound and a Hölder
constant, multiplying each by the integral of the kernel norm. This applies to truncated planar
Cauchy and Newtonian kernels, and to the normalized smoothing kernels used to pass their
estimates from smooth to Hölder data. An even kernel with vanishing integral sees only the second
differences `f (x + h) + f (x - h) - 2 f x` of the function it is convolved with, so a bound
`H ‖h‖ ^ s` on them bounds the convolution by `H` times the `s`-th moment of the kernel; this is
how the Littlewood–Paley blocks of a function in the Zygmund class are estimated.
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

omit [OpensMeasurableSpace E] [SecondCountableTopologyEither E F] in
/-- **Even kernels with vanishing integral see second differences.** Let `K` be an even integrable
scalar kernel with `∫ K = 0` and finite `s`-th moment, and let the second differences of `f`
satisfy `‖f (x + h) + f (x - h) - 2 f x‖ ≤ H ‖h‖ ^ s`. If `z ↦ K z • f (w - z)` is integrable,
then `‖∫ K z • f (w - z) dz‖ ≤ H ∫ ‖z‖ ^ s ‖K z‖ dz`. -/
theorem norm_integral_kernel_smul_sub_le_of_norm_add_add_sub_two_nsmul_le [CompleteSpace F]
    [MeasurableNeg E] [μ.IsNegInvariant] (hK : Integrable K μ) (heven : Function.Even K)
    (hK0 : ∫ z, K z ∂μ = 0) {H s : ℝ}
    (hf : ∀ x h, ‖f (x + h) + f (x - h) - 2 • f x‖ ≤ H * ‖h‖ ^ s)
    (hm : Integrable (fun z ↦ ‖z‖ ^ s * ‖K z‖) μ) {w : E}
    (hw : Integrable (fun z ↦ K z • f (w - z)) μ) :
    ‖∫ z, K z • f (w - z) ∂μ‖ ≤ H * ∫ z, ‖z‖ ^ s * ‖K z‖ ∂μ := by
  -- Averaging the integral with its reflection `z ↦ -z` replaces `f (w - z)` by half the second
  -- difference `f (w + z) + f (w - z) - 2 f w`.
  have heven' : ∀ z, K (-z) = K z := heven
  have hw' : Integrable (fun z ↦ K z • f (w + z)) μ := by
    simpa [heven', sub_neg_eq_add] using hw.comp_neg
  have hc : Integrable (fun z ↦ K z • f w) μ := hK.smul_const _
  have hzero : ∫ z, K z • f w ∂μ = 0 := by rw [integral_smul_const, hK0, zero_smul]
  -- Reflecting `z ↦ -z` and using that `K` is even turns `f (w - z)` into `f (w + z)`.
  have hrefl : ∫ z, K z • f (w - z) ∂μ = ∫ z, K z • f (w + z) ∂μ := by
    rw [← integral_neg_eq_self]
    simp only [heven', sub_neg_eq_add]
  have heq : (∫ z, K z • f (w - z) ∂μ) + ∫ z, K z • f (w - z) ∂μ =
      ∫ z, K z • (f (w + z) + f (w - z) - 2 • f w) ∂μ := by
    simp only [two_nsmul, smul_sub, smul_add]
    have hsum : Integrable (fun z ↦ K z • f (w + z) + K z • f (w - z)) μ := hw'.add hw
    have hcc : Integrable (fun z ↦ K z • f w + K z • f w) μ := hc.add hc
    rw [integral_sub hsum hcc, integral_add hw' hw, integral_add hc hc, hzero, add_zero,
      sub_zero, hrefl]
  have hle : ‖∫ z, K z • (f (w + z) + f (w - z) - 2 • f w) ∂μ‖ ≤
      ∫ z, H * (‖z‖ ^ s * ‖K z‖) ∂μ :=
    norm_integral_le_of_norm_le (hm.const_mul _) (ae_of_all _ fun z ↦ by
      rw [norm_smul]
      nlinarith [mul_le_mul_of_nonneg_left (hf w z) (norm_nonneg (K z))])
  have h2 : ‖(∫ z, K z • f (w - z) ∂μ) + ∫ z, K z • f (w - z) ∂μ‖ =
      2 * ‖∫ z, K z • f (w - z) ∂μ‖ := by
    rw [← two_smul 𝕜, norm_smul, RCLike.norm_two]
  rw [integral_const_mul, ← heq, h2] at hle
  linarith [norm_nonneg (∫ z, K z • f (w - z) ∂μ)]

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
