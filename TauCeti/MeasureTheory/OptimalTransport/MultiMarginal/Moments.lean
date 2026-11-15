/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Basic
public import TauCeti.Probability.Moments.Covariance
import TauCeti.Analysis.InnerProductSpace.CompleteSquare

/-!
# Moments of multi-marginal couplings

Let `γ` be a multi-marginal coupling of finitely many laws `μ j` on a common normed space, each
with finite moments of the relevant order. This file records the integrability of weighted sums
of the coordinates of `γ` and of the quadratic multi-marginal cost
`∑ i, w i * ‖∑ j, w j • x j - x i‖ ^ 2`, and, for laws on `ℝⁿ` and weights summing to `1`, the
mean of that cost in terms of the means and covariance matrices of the laws `μ j` and of the
second moment of the centred weighted mean `∑ j, w j • (x j - 𝔼 μ j)`.

## Main statements

* `TauCeti.Measure.IsMultiCoupling.memLp_sum_smul_sub`: weighted sums of shifted coordinates
  inherit the moments of the marginals.
* `TauCeti.Measure.IsMultiCoupling.integrable_sum_mul_norm_sum_smul_sub_sq`: the quadratic
  multi-marginal cost is integrable.
* `TauCeti.Measure.IsMultiCoupling.integral_sum_mul_norm_sum_smul_sub_sq`: the weighted variance
  decomposition of the quadratic multi-marginal cost.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Measure.IsMultiCoupling

variable {J : Type*} [Fintype J]

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : J → Measure E} {γ : Measure (J → E)}

/-- Under a finite multi-marginal coupling of laws with finite `p`-th moments, a weighted sum of
shifted coordinates `∑ j, a j • (x j - c j)` has a finite `p`-th moment. -/
theorem memLp_sum_smul_sub [IsFiniteMeasure γ] (hγ : IsMultiCoupling γ μ) {p : ℝ≥0∞}
    (hμ : ∀ j, MemLp id p (μ j)) (a : J → ℝ) (c : J → E) :
    MemLp (fun x ↦ ∑ j, a j • (x j - c j)) p γ :=
  memLp_finsetSum _ fun j _ ↦
    ((hγ.memLp_comp_eval j (hμ j)).sub (memLp_const (c j))).const_smul (a j)

/-- The quadratic multi-marginal cost `∑ i, a i * ‖∑ j, w j • x j - x i‖ ^ 2` of a multi-marginal
coupling of laws with finite second moments is integrable. -/
theorem integrable_sum_mul_norm_sum_smul_sub_sq (hγ : IsMultiCoupling γ μ)
    (hμ : ∀ j, MemLp id 2 (μ j)) (a w : J → ℝ) :
    Integrable (fun x ↦ ∑ i, a i * ‖∑ j, w j • x j - x i‖ ^ 2) γ :=
  integrable_finsetSum _ fun i _ ↦ by
    have hi : MemLp (fun x : J → E ↦ ∑ j, w j • x j - x i) 2 γ :=
      (memLp_finsetSum _ fun j _ ↦ (hγ.memLp_comp_eval j (hμ j)).const_smul (w j)).sub
        (hγ.memLp_comp_eval i (hμ i))
    exact ((memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).1 hi).const_mul _

end NormedSpace

variable {ι : Type*} [Fintype ι] {μ : J → Measure (EuclideanSpace ℝ ι)}
  {γ : Measure (J → EuclideanSpace ℝ ι)}

/-- **The weighted variance decomposition of a multi-marginal coupling.** For weights summing to
`1`, the quadratic multi-marginal cost `∑ i, w i * ‖∑ j, w j • x j - x i‖ ^ 2` of a multi-marginal
coupling of laws with finite second moments, means `m i` and covariance matrices `C i` has mean
`∑ i, w i * (‖m i - mbar‖ ^ 2 + tr C i)` minus the second moment of the centred weighted mean
`∑ j, w j • (x j - m j)`, where `mbar = ∑ j, w j • m j`. -/
theorem integral_sum_mul_norm_sum_smul_sub_sq (hγ : IsMultiCoupling γ μ)
    [∀ j, IsProbabilityMeasure (μ j)] (hμ : ∀ j, MemLp id 2 (μ j)) {w : J → ℝ}
    (hw : ∑ j, w j = 1) :
    ∫ x, ∑ i, w i * ‖∑ j, w j • x j - x i‖ ^ 2 ∂γ =
      ∑ i, w i * (‖∫ y, y ∂μ i - ∑ j, w j • ∫ y, y ∂μ j‖ ^ 2 + (covMatrix (μ i)).trace) -
        ∫ x, ‖∑ j, w j • (x j - ∫ y, y ∂μ j)‖ ^ 2 ∂γ := by
  obtain ⟨j₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  have := hγ.isProbabilityMeasure j₀
  set m : J → EuclideanSpace ℝ ι := fun j ↦ ∫ y, y ∂μ j
  set mbar := ∑ i, w i • m i
  set W : (J → EuclideanSpace ℝ ι) → EuclideanSpace ℝ ι := fun x ↦ ∑ j, w j • (x j - m j)
  -- The pointwise weighted variance decomposition about `mbar`.
  have hF (x : J → EuclideanSpace ℝ ι) : ∑ i, w i * ‖∑ j, w j • x j - x i‖ ^ 2 =
      ∑ i, w i * ‖x i - mbar‖ ^ 2 - ‖W x‖ ^ 2 := by
    have h := Finset.univ.sum_mul_norm_sub_sq_eq hw mbar x
    have hWx : W x = ∑ j, w j • x j - mbar := by
      simp only [W, mbar, smul_sub, Finset.sum_sub_distrib]
    simp only [norm_sub_rev mbar] at h
    rw [hWx]
    linarith
  have hsq (i : J) : Integrable (fun x : J → EuclideanSpace ℝ ι ↦ ‖x i - mbar‖ ^ 2) γ :=
    have hi := (hγ.memLp_comp_eval i (hμ i)).sub (memLp_const mbar)
    (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).1 hi
  have hW : MemLp W 2 γ := hγ.memLp_sum_smul_sub hμ w m
  have hWsq : Integrable (fun x ↦ ‖W x‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).1 hW
  rw [integral_congr_ae (.of_forall hF), integral_sub
    (integrable_finsetSum _ fun i _ ↦ (hsq i).const_mul _) hWsq,
    integral_finsetSum _ fun i _ ↦ (hsq i).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, hγ.integral_comp_eval i (f := fun y ↦ ‖y - mbar‖ ^ 2)
    (by fun_prop), integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix _ (hμ i)]

end TauCeti.Measure.IsMultiCoupling
