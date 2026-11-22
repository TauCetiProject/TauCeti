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

/-- On a probability space, a weighted sum of centered truncation residuals over a finite set
is integrable. Its mean norm is bounded by twice the sum of discarded norm integrals times the
coefficient bound. -/
theorem integrable_and_integral_norm_sum_mul_centeredTruncation_residual_le
    {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    {P : Measure Ω} [IsProbabilityMeasure P] {s : Finset ι}
    {W : ι → Ω → ℝ} (hW : ∀ i ∈ s, Integrable (W i) P) (a : ι → 𝕜)
    {C : ℝ} (ha : ∀ i ∈ s, ‖a i‖ ≤ C) (r : ℝ≥0) :
    let D (i : ι) (ω : Ω) :=
      W i ω - (∫ y, W i y ∂P) - centeredTruncation (W i) P r ω
    Integrable (fun ω ↦ ∑ i ∈ s, a i * (D i ω : 𝕜)) P ∧
      (∫ ω, ‖∑ i ∈ s, a i * (D i ω : 𝕜)‖ ∂P) ≤ C * (2 * ∑ i ∈ s,
        ∫ ω, {ω | (r : ℝ) < ‖W i ω‖}.indicator (fun ω ↦ ‖W i ω‖) ω ∂P) := by
  intro D
  have hD (i : ι) (hi : i ∈ s) : Integrable (fun ω ↦ a i * (D i ω : 𝕜)) P := by
    have hi : Integrable (D i) P := ((hW i hi).sub (integrable_const _)).sub
      (((hW i hi).aestronglyMeasurable.memLp_centeredTruncation r).integrable one_le_two)
    exact ((RCLike.ofRealCLM (K := 𝕜)).integrable_comp hi).const_mul _
  have hsum := integrable_finsetSum s hD
  refine ⟨hsum, (integral_mono hsum.norm
    (integrable_finsetSum s fun i hi ↦ (hD i hi).norm) (fun _ ↦ norm_sum_le _ _)).trans ?_⟩
  rw [integral_finsetSum _ (fun i hi ↦ (hD i hi).norm), ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  simp only [norm_mul, RCLike.norm_ofReal, ← Real.norm_eq_abs, integral_const_mul]
  rw [mul_assoc]
  exact mul_le_mul (ha i hi) ((hW i hi).integral_norm_sub_integral_sub_centeredTruncation_le r)
    (integral_nonneg fun ω ↦ norm_nonneg (D i ω)) ((norm_nonneg _).trans (ha i hi))

end TauCeti.Probability

namespace TauCeti

open ProbabilityTheory Finset TauCeti.Probability

/-- Mean-norm bound for a weighted sum over a finite set of centered pairwise independent real
variables on a probability space.
The cutoff controls the retained part and the tail integrals bound the discarded part. -/
theorem _root_.Set.Pairwise.integral_norm_sum_mul_sub_integral_le {Ω ι 𝕜 : Type*}
    [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω} [IsProbabilityMeasure P] {s : Finset ι}
    {W : ι → Ω → ℝ} (hWi : (s : Set ι).Pairwise fun i j ↦ IndepFun (W i) (W j) P)
    (hW : ∀ i ∈ s, Integrable (W i) P) (a : ι → 𝕜) {C v : ℝ}
    (ha : ∀ i ∈ s, ‖a i‖ ≤ C) (hv : ∀ i ∈ s, ∫ ω, ‖W i ω‖ ∂P ≤ v) (r : ℝ≥0) :
    (∫ ω, ‖∑ i ∈ s, a i * ((W i ω - ∫ y, W i y ∂P : ℝ) : 𝕜)‖ ∂P) ≤
      C * (Real.sqrt ((r : ℝ) * #s * v) +
        2 * ∑ i ∈ s, ∫ ω, {ω | (r : ℝ) < ‖W i ω‖}.indicator (fun ω ↦ ‖W i ω‖) ω ∂P) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  have hC := (norm_nonneg (a i)).trans (ha i hi)
  let T (i : ι) := centeredTruncation (W i) P r
  let Y (i : ι) (ω : Ω) := a i * (T i ω : 𝕜)
  let D (i : ι) (ω : Ω) := W i ω - (∫ y, W i y ∂P) - T i ω
  have hY (i : ι) (hi : i ∈ s) : MemLp (Y i) 2 P :=
    ((hW i hi).aestronglyMeasurable.memLp_centeredTruncation r).ofReal.const_mul _
  have hYi : (s : Set ι).Pairwise fun i j ↦ IndepFun (Y i) (Y j) P := fun i hi j hj hij ↦
    ((hWi hi hj hij).centeredTruncation r r).comp (φ := fun z : ℝ ↦ a i * (z : 𝕜))
      (ψ := fun z : ℝ ↦ a j * (z : 𝕜)) (by fun_prop) (by fun_prop)
  have hmean (i : ι) (hi : i ∈ s) : ∫ ω, Y i ω ∂P = 0 := by
    simp only [Y, integral_const_mul, integral_ofReal, T,
      (hW i hi).aestronglyMeasurable.integral_centeredTruncation, RCLike.ofReal_zero, mul_zero]
  have hsmall : (∫ ω, ‖∑ i ∈ s, Y i ω‖ ∂P) ≤ C * Real.sqrt ((r : ℝ) * #s * v) := by
    refine (TauCeti.integral_norm_sum_le_of_pairwise_indepFun hY hmean hYi
      (v := C ^ 2 * ((r : ℝ) * v)) (fun i hi ↦ ?_)).trans_eq ?_
    · simp only [Y, norm_mul, RCLike.norm_ofReal, mul_pow, integral_const_mul]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (ha i hi) 2)
        (((hW i hi).integral_norm_centeredTruncation_sq_le_mul r).trans
          (mul_le_mul_of_nonneg_left (hv i hi) r.coe_nonneg))
        (integral_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _)
    · calc
        _ = Real.sqrt (C ^ 2 * ((r : ℝ) * #s * v)) := by congr 1; ring
        _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
  have hdiscard := integrable_and_integral_norm_sum_mul_centeredTruncation_residual_le hW a ha r
  have hsum (ω : Ω) : (∑ i ∈ s, a i * ((W i ω - ∫ y, W i y ∂P : ℝ) : 𝕜)) =
      (∑ i ∈ s, Y i ω) + ∑ i ∈ s, a i * (D i ω : 𝕜) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Y, D, RCLike.ofReal_sub]
    ring
  simp_rw [hsum, mul_add]
  have ht := (memLp_finsetSum s hY).integrable one_le_two
  exact (ht.integral_norm_add_le hdiscard.1).trans (add_le_add hsmall hdiscard.2)

end TauCeti
