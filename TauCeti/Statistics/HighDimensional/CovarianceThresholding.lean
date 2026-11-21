/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SampleCovariance.EntrywiseConcentration
public import TauCeti.Analysis.Matrix.HardThreshold

/-!
# Hard-thresholded covariance estimation

If every entry of a sample covariance is within `λ` of the corresponding population entry,
thresholding at `λ` removes every entry outside the population support and incurs an error
of at most `2 * λ` at each remaining entry. Entrywise domination and the Schur test convert
this into an operator norm bound. Entrywise concentration supplies a choice of threshold
for independent observations with sub-Gaussian coordinates.

## References

* M. J. Wainwright, *High-Dimensional Statistics* (2019), Theorem 6.23 and Corollary 6.24.
* P. J. Bickel and E. Levina, *Covariance regularization by thresholding* (2008), Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator NNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω ι p : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype p] [DecidableEq p]
  {μ : Measure Ω} {x : ι → Ω → p → ℝ} {c : ℝ≥0} {cov : Matrix p p ℝ}

/-- Hard thresholding at the simultaneous entrywise confidence threshold yields an
operator norm error of at most twice that threshold times the row sparsity. -/
theorem measureReal_hardThreshold_sampleSecondMoment_sub_le
    (hindep : iIndepFun x μ) (hsub : ∀ a i, HasSubgaussianMGF (fun ω ↦ x a ω i) c μ)
    (hcov : ∀ a i j, ∫ ω, x a ω i * x a ω j ∂μ = cov i j)
    {s : ℕ} (hs : ∀ i, (Finset.univ.filter fun j ↦ cov i j ≠ 0).card ≤ s)
    (hn : log (Fintype.card p) ≤ Fintype.card ι) (δ : ℝ) :
    let threshold := (c : ℝ) * (13120 * √(log (Fintype.card p) / Fintype.card ι) + δ)
    1 - 2 * exp (-(Fintype.card ι / 6560) * min δ (δ ^ 2)) ≤ μ.real {ω |
      ‖(TauCeti.sampleSecondMoment (fun a ↦ x a ω)).hardThreshold threshold - cov‖ ≤
        2 * threshold * s} := by
  intro threshold
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_of_isEmpty, Nat.cast_zero, zero_div, neg_zero, zero_mul, exp_zero,
      mul_one]
    exact (by norm_num : (1 : ℝ) - 2 ≤ 0).trans measureReal_nonneg
  rcases lt_or_ge δ 0 with hδ | hδ
  · have hrate : 0 ≤ -(Fintype.card ι / 6560 : ℝ) * min δ (δ ^ 2) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity))
        ((min_le_left _ _).trans hδ.le)
    have hfailure : 1 - 2 * exp (-(Fintype.card ι / 6560) * min δ (δ ^ 2)) ≤ 0 := by
      linarith [Real.one_le_exp hrate]
    exact hfailure.trans measureReal_nonneg
  have hcovHermitian : cov.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j ↦ ?_
    let a : ι := Classical.choice hι
    rw [star_trivial, ← hcov a j i, ← hcov a i j]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ ↦ mul_comm _ _)
  have hthreshold : 0 ≤ threshold := by dsimp [threshold]; positivity
  refine (hindep.one_sub_exp_le_measureReal_forall_abs_sampleSecondMoment_sub_le
    hsub hcov hn δ).trans (measureReal_mono ?_)
  intro ω hω
  have hentry := (TauCeti.sampleSecondMoment (fun a ↦ x a ω)).l2_opNorm_hardThreshold_sub_le cov
    (fun i j ↦ by simpa only [Real.norm_eq_abs] using hω i j)
  exact hentry.trans (mul_le_mul_of_nonneg_left (hcovHermitian.l2_opNorm_supportPattern_le hs)
    (mul_nonneg (by norm_num) hthreshold))

/-- With threshold `13121 * c * √(log p / n)` the hard-thresholded sample covariance of
independent sub-Gaussian observations has operator norm error at most the threshold times
twice the row sparsity, with failure probability at most `2 * p ^ (-1 / 6560)`. -/
theorem hardThreshold_covariance_prob
    (hindep : iIndepFun x μ) (hsub : ∀ a i, HasSubgaussianMGF (fun ω ↦ x a ω i) c μ)
    (hcov : ∀ a i j, ∫ ω, x a ω i * x a ω j ∂μ = cov i j)
    {s : ℕ} (hs : ∀ i, (Finset.univ.filter fun j ↦ cov i j ≠ 0).card ≤ s)
    (hn : log (Fintype.card p) ≤ Fintype.card ι) :
    let threshold := (c : ℝ) * 13121 * √(log (Fintype.card p) / Fintype.card ι)
    1 - 2 * (Fintype.card p : ℝ) ^ (-1 / 6560 : ℝ) ≤ μ.real {ω |
      ‖(TauCeti.sampleSecondMoment (fun a ↦ x a ω)).hardThreshold threshold - cov‖ ≤
        2 * threshold * s} := by
  intro threshold
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  let P := (Fintype.card p : ℝ)
  let N := (Fintype.card ι : ℝ)
  rcases le_or_gt (Fintype.card p) 1 with hsmall | hlarge
  · interval_cases hP : Fintype.card p
    · have : IsEmpty p := Fintype.card_eq_zero_iff.mp hP
      have hzero (ω : Ω) :
          (TauCeti.sampleSecondMoment (fun a ↦ x a ω)).hardThreshold threshold - cov = 0 :=
        Subsingleton.elim _ _
      have hnonneg : 0 ≤ 2 * threshold * (s : ℝ) := by dsimp [threshold]; positivity
      simp [hzero, hnonneg, probReal_univ]
    · simp only [Nat.cast_one, one_rpow]
      exact (by norm_num : (1 : ℝ) - 2 * 1 ≤ 0).trans measureReal_nonneg
  have hP : 1 < P := Nat.one_lt_cast.mpr hlarge
  have hlog : 0 < log P := Real.log_pos hP
  have hN : 0 < N := hlog.trans_le hn
  let δ := √(log P / N)
  have hδ : 0 < δ := Real.sqrt_pos.2 (div_pos hlog hN)
  have hsq : δ ^ 2 = log P / N := Real.sq_sqrt (div_nonneg hlog.le hN.le)
  have hδ₁ : δ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_one hN).2 hn)
  have hrate : -(N / 6560) * min δ (δ ^ 2) = log P * (-1 / 6560) := by
    rw [min_eq_right (by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ₁)]), hsq]
    field_simp
  have hthresh : (c : ℝ) * (13120 * δ + δ) = threshold := by
    dsimp [threshold, δ, P, N]
    ring
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hP), ← hrate, ← hthresh]
  exact hindep.measureReal_hardThreshold_sampleSecondMoment_sub_le hsub hcov hs hn δ

end ProbabilityTheory.iIndepFun
