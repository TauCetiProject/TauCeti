/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Probability.Moments.SampleMean
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted sums of centered truncations

For pairwise independent real variables, the weighted mean absolute fluctuation splits into a
second-moment bound for the truncated variables and a first-moment bound for the discarded tails.
-/

public section

open MeasureTheory
open scoped NNReal

namespace TauCeti.Probability

/-- On a probability space, a weighted sum of centered truncation residuals is integrable.
Its mean norm is bounded by twice the sum of discarded norm integrals times the
coefficient bound. -/
theorem integrable_and_integral_norm_sum_mul_centeredTruncation_residual_le
    {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → Ω → ℝ} (hW : ∀ i, Integrable (W i) P) (a : ι → 𝕜)
    {C : ℝ} (ha : ∀ i, ‖a i‖ ≤ C) (r : ℝ≥0) :
    let D (i : ι) (ω : Ω) :=
      W i ω - (∫ y, W i y ∂P) - centeredTruncation (W i) P r ω
    Integrable (fun ω ↦ ∑ i, a i * (D i ω : 𝕜)) P ∧
      (∫ ω, ‖∑ i, a i * (D i ω : 𝕜)‖ ∂P) ≤ C * (2 * ∑ i,
        ∫ ω, {ω | (r : ℝ) < ‖W i ω‖}.indicator (fun ω ↦ ‖W i ω‖) ω ∂P) := by
  intro D
  have hD (i : ι) : Integrable (fun ω ↦ a i * (D i ω : 𝕜)) P := by
    have hi : Integrable (D i) P := ((hW i).sub (integrable_const _)).sub
      (((hW i).aestronglyMeasurable.memLp_centeredTruncation r).integrable one_le_two)
    exact ((RCLike.ofRealCLM (K := 𝕜)).integrable_comp hi).const_mul _
  have hsum := integrable_finsetSum Finset.univ fun i _ ↦ hD i
  refine ⟨hsum, (integral_mono hsum.norm
    (integrable_finsetSum Finset.univ fun i _ ↦ (hD i).norm) (fun _ ↦ norm_sum_le _ _)).trans ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ (hD i).norm), ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  simp only [norm_mul, RCLike.norm_ofReal, ← Real.norm_eq_abs, integral_const_mul]
  rw [mul_assoc]
  exact mul_le_mul (ha i) ((hW i).integral_norm_sub_integral_sub_centeredTruncation_le r)
    (integral_nonneg fun ω ↦ norm_nonneg (D i ω)) ((norm_nonneg _).trans (ha i))

end TauCeti.Probability

namespace TauCeti

open ProbabilityTheory Finset TauCeti.Probability

/-- Mean-norm bound for a weighted sum of centered pairwise independent real variables on a
probability space.
The cutoff controls the retained part and the tail integrals bound the discarded part. -/
theorem _root_.Pairwise.integral_norm_sum_mul_sub_integral_le {Ω ι 𝕜 : Type*}
    [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → Ω → ℝ} (hWi : Pairwise fun i j ↦ IndepFun (W i) (W j) P)
    (hW : ∀ i, Integrable (W i) P) (a : ι → 𝕜) {C v : ℝ}
    (ha : ∀ i, ‖a i‖ ≤ C) (hv : ∀ i, ∫ ω, ‖W i ω‖ ∂P ≤ v) (r : ℝ≥0) :
    (∫ ω, ‖∑ i, a i * ((W i ω - ∫ y, W i y ∂P : ℝ) : 𝕜)‖ ∂P) ≤
      C * (Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
        2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖W i ω‖}.indicator (fun ω ↦ ‖W i ω‖) ω ∂P) := by
  classical
  cases isEmpty_or_nonempty ι
  · simp
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hC := (norm_nonneg (a i)).trans (ha i)
  let T (i : ι) := centeredTruncation (W i) P r
  let Y (i : ι) (ω : Ω) := a i * (T i ω : 𝕜)
  let D (i : ι) (ω : Ω) := W i ω - (∫ y, W i y ∂P) - T i ω
  have hY (i : ι) : MemLp (Y i) 2 P :=
    ((hW i).aestronglyMeasurable.memLp_centeredTruncation r).ofReal.const_mul _
  have hYi : Pairwise fun i j ↦ IndepFun (Y i) (Y j) P := by
    intro i j hij
    exact ((hWi hij).centeredTruncation r r).comp (φ := fun z : ℝ ↦ a i * (z : 𝕜))
      (ψ := fun z : ℝ ↦ a j * (z : 𝕜)) (by fun_prop) (by fun_prop)
  have hmean (i : ι) : ∫ ω, Y i ω ∂P = 0 := by
    simp only [Y, integral_const_mul, integral_ofReal, T,
      (hW i).aestronglyMeasurable.integral_centeredTruncation, RCLike.ofReal_zero, mul_zero]
  have hsmall : (∫ ω, ‖∑ i, Y i ω‖ ∂P) ≤
      C * Real.sqrt ((r : ℝ) * Fintype.card ι * v) := by
    refine (TauCeti.integral_norm_sum_le_of_pairwise_indepFun (s := univ)
      (fun i _ ↦ hY i) (fun i _ ↦ hmean i) (fun _ _ _ _ hij ↦ hYi hij)
      (v := C ^ 2 * ((r : ℝ) * v)) (fun i _ ↦ ?_)).trans_eq ?_
    · simp only [Y, norm_mul, RCLike.norm_ofReal, mul_pow, integral_const_mul]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (ha i) 2)
        (((hW i).integral_norm_centeredTruncation_sq_le_mul r).trans
          (mul_le_mul_of_nonneg_left (hv i) r.coe_nonneg))
        (integral_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _)
    · rw [card_univ]
      calc
        _ = Real.sqrt (C ^ 2 * ((r : ℝ) * Fintype.card ι * v)) := by congr 1; ring
        _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
  have hdiscard := integrable_and_integral_norm_sum_mul_centeredTruncation_residual_le hW a ha r
  have hsum (ω : Ω) : (∑ i, a i * ((W i ω - ∫ y, W i y ∂P : ℝ) : 𝕜)) =
      (∑ i, Y i ω) + ∑ i, a i * (D i ω : 𝕜) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Y, D, RCLike.ofReal_sub]
    ring
  simp_rw [hsum, mul_add]
  have ht := (memLp_finsetSum univ fun i _ ↦ hY i).integrable one_le_two
  exact (ht.integral_norm_add_le hdiscard.1).trans (add_le_add hsmall hdiscard.2)

end TauCeti
