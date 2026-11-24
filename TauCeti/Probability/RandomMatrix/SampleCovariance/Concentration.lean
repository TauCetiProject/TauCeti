/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrix.SampleCovariance.ExpectedSpectralMeasure
public import TauCeti.Probability.Independence.Matrix

import TauCeti.Analysis.Matrix.SampleCovariance.Rank
import TauCeti.Analysis.Matrix.SpectralMeasure.RankPerturbation
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
import TauCeti.Probability.McDiarmid.Independent
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Concentration of sample covariance spectral measures

Replacing one row or column of a rectangular data matrix changes its sample covariance by
rank at most two. The rank inequality and McDiarmid's inequality consequently control the
empirical cumulative distribution function with independent rows or independent columns,
without any entry moment assumptions.

With independent rows and summable tails in the row dimension, pointwise fluctuations vanish
almost surely. Weak convergence of the expected spectral measures is then equivalent to
almost sure weak convergence to the same deterministic law. This also works for limits with
atoms, including the Marchenko–Pastur law above aspect ratio one.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  second edition, Springer, 2010, §3.3 and Theorem A.43.
* C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics 141 (1989).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω p n 𝕜 : Type*} [MeasurableSpace Ω] [Fintype p] [DecidableEq p] [Nonempty p]
  [Fintype n] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {P : Measure Ω} [IsProbabilityMeasure P]

private theorem measureReal_abs_cdf_sampleCovariance_sub_expected_ge_le
    {ι E : Type*} [Fintype ι] [MeasurableSpace E] {Y : ι → Ω → E} (hind : iIndepFun Y P)
    (hY : ∀ i, AEMeasurable (Y i) P) {F : (ι → E) → Matrix p n 𝕜} (hF : Measurable F)
    (hrank : ∀ (i : ι) (a b : ι → E), (∀ j ≠ i, a j = b j) → (F a - F b).rank ≤ 1)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |cdf ((F (fun i ↦ Y i ω)).sampleCovariance.spectralMeasure
        (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) x -
      cdf (expectedCovarianceSpectralMeasure
        (hF.comp_aemeasurable (aemeasurable_pi_iff.2 hY)) : Measure ℝ) x|} ≤
      2 * Real.exp (-(t ^ 2) * (Fintype.card p : ℝ) ^ 2 / (2 * Fintype.card ι)) := by
  let f (a : ι → E) := cdf ((F a).sampleCovariance.spectralMeasure
    (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) x
  have hf : Measurable f := by
    simp only [f, cdf_eq_real, measureReal_def]
    exact ((Measure.measurable_coe measurableSet_Iic).comp
      (measurable_subtypeVal.comp
        (Matrix.measurable_spectralMeasure_sampleCovariance.comp hF))).ennreal_toReal
  have hdiff (i : ι) (a b : ι → E) (hab : ∀ j ≠ i, a j = b j) :
      |f a - f b| ≤ ((2 / (Fintype.card p : ℝ≥0) : ℝ≥0) : ℝ) := by
    simp only [f, cdf_eq_real, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    refine ((Matrix.isHermitian_sampleCovariance (F a)).abs_spectralMeasure_Iic_sub_le_rank_div_card
      (Matrix.isHermitian_sampleCovariance (F b)) x).trans ?_
    gcongr
    exact_mod_cast (Matrix.rank_sampleCovariance_sub_le (F a) (F b)).trans
      (Nat.mul_le_mul_left 2 (hrank i a b hab))
  rw [cdf_expectedCovarianceSpectralMeasure]
  have htail := hind.measureReal_abs_sub_integral_ge_le_of_bounded_differences hY f hf
    (fun _ ↦ 2 / (Fintype.card p : ℝ≥0)) hdiff ht
  have hrates : -2 * t ^ 2 / (∑ _ : ι, ((2 / (Fintype.card p : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) =
      -(t ^ 2) * (Fintype.card p : ℝ) ^ 2 / (2 * Fintype.card ι) := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow, inv_inv]
    ring
  rwa [hrates] at htail

variable {X : Ω → Matrix p n 𝕜}

/-- With independent rows, deviations of the empirical CDF from its mean have Gaussian tails
with exponent −p t²/2, where p is the number of rows. -/
theorem measureReal_abs_cdf_sampleCovariance_sub_expected_ge_le_of_indep_row
    (hX : AEMeasurable X P) (hind : iIndepFun (fun i ω ↦ (X ω).row i) P)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |cdf ((X ω).sampleCovariance.spectralMeasure
        (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) x -
      cdf (expectedCovarianceSpectralMeasure hX : Measure ℝ) x|} ≤
      2 * Real.exp (-(t ^ 2) * Fintype.card p / 2) := by
  have hy (i : p) : AEMeasurable (fun ω ↦ (X ω).row i) P :=
    aemeasurable_pi_iff.2 fun _ ↦ Matrix.measurable_apply.comp_aemeasurable hX
  have htail := measureReal_abs_cdf_sampleCovariance_sub_expected_ge_le hind hy
    (F := Matrix.of) (Matrix.ofMeasurableEquiv p n 𝕜).measurable
    (fun i a b hab ↦ Matrix.rank_sub_le_one_of_row_eq (Matrix.of a) (Matrix.of b) i hab)
    x ht
  have hcard : (Fintype.card p : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hrates : -(t ^ 2) * (Fintype.card p : ℝ) ^ 2 / (2 * Fintype.card p) =
      -(t ^ 2) * Fintype.card p / 2 := by field_simp [hcard]
  rwa [hrates] at htail

/-- With independent columns, deviations of the empirical CDF from its mean have Gaussian
tails with exponent −p² t²/(2n), where the data have p rows and n columns. -/
theorem measureReal_abs_cdf_sampleCovariance_sub_expected_ge_le_of_indep_col
    (hX : AEMeasurable X P) (hind : iIndepFun (fun j ω ↦ (X ω).col j) P)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |cdf ((X ω).sampleCovariance.spectralMeasure
        (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) x -
      cdf (expectedCovarianceSpectralMeasure hX : Measure ℝ) x|} ≤
      2 * Real.exp (-(t ^ 2) * (Fintype.card p : ℝ) ^ 2 / (2 * Fintype.card n)) := by
  have hy (j : n) : AEMeasurable (fun ω ↦ (X ω).col j) P :=
    aemeasurable_pi_iff.2 fun i ↦ by
      simpa only [Matrix.col_apply, Function.comp_def] using
        (Matrix.measurable_apply (i := i) (j := j)).comp_aemeasurable hX
  exact measureReal_abs_cdf_sampleCovariance_sub_expected_ge_le hind hy
    (F := fun a ↦ Matrix.of fun i j ↦ a j i)
    (.of_eval_matrix _ fun i j ↦ (measurable_pi_apply i).comp (measurable_pi_apply j))
    (fun j a b hab ↦ Matrix.rank_sub_le_one_of_col_eq
      (Matrix.of fun i k ↦ a k i) (Matrix.of fun i k ↦ b k i) j hab)
    x ht

section Sequence

variable {p n : ℕ → Type*} [∀ m, Fintype (p m)] [∀ m, DecidableEq (p m)]
  [∀ m, Nonempty (p m)] [∀ m, Fintype (n m)]
  {X : (m : ℕ) → Ω → Matrix (p m) (n m) 𝕜}

/-- At each fixed threshold, the CDF of the random covariance spectrum and the CDF of its
expected measure differ by an almost surely vanishing error. The row dimension must grow
fast enough to make the exponential concentration bounds summable. -/
theorem ae_tendsto_cdf_sampleCovariance_sub_expected
    (hX : ∀ m, AEMeasurable (X m) P) (hind : ∀ m, iIndepFun (fun i ω ↦ (X m ω).row i) P)
    (hdim : ∀ a : ℝ, 0 < a → Summable (fun m ↦ Real.exp (-a * Fintype.card (p m))))
    (x : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ cdf ((X m ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) x -
        cdf (expectedCovarianceSpectralMeasure (hX m) : Measure ℝ) x) atTop (𝓝 0) := by
  let D (m : ℕ) (ω : Ω) := cdf ((X m ω).sampleCovariance.spectralMeasure
    (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) x -
      cdf (expectedCovarianceSpectralMeasure (hX m) : Measure ℝ) x
  have hbc (j : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, |D m ω| < (j + 1 : ℝ)⁻¹ := by
    let t := (j + 1 : ℝ)⁻¹
    have ht : 0 < t := by positivity
    have hsum := (hdim (t ^ 2 / 2) (by positivity)).mul_left 2
    have htail : Summable (fun m ↦ P.real {ω | t ≤ |D m ω|}) := by
      refine hsum.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) fun m ↦ ?_
      calc
        _ ≤ 2 * Real.exp (-(t ^ 2) * Fintype.card (p m) / 2) :=
          measureReal_abs_cdf_sampleCovariance_sub_expected_ge_le_of_indep_row
            (hX m) (hind m) x ht.le
        _ = _ := by congr 2; ring
    have hfinite : (∑' m, P {ω | t ≤ |D m ω|}) ≠ ∞ := by
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        htail.tsum_ofReal_ne_top
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfinite
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with m hm
  simpa only [Real.dist_eq, sub_zero, D] using hm.trans (by simpa only [one_div] using hj)

/-- For sample covariance matrices with independent rows and summable concentration bounds,
almost sure weak convergence to a deterministic law is equivalent to weak convergence of the
expected measures. The matrix sizes may be coupled arbitrarily on the common sample space. -/
theorem ae_tendsto_spectralMeasure_sampleCovariance_iff_tendsto_expected
    (hX : ∀ m, AEMeasurable (X m) P) (hind : ∀ m, iIndepFun (fun i ω ↦ (X m ω).row i) P)
    (hdim : ∀ a : ℝ, 0 < a → Summable (fun m ↦ Real.exp (-a * Fintype.card (p m))))
    {μ : ProbabilityMeasure ℝ} :
    (∀ᵐ ω ∂P, Tendsto (fun m ↦ (X m ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance _)) atTop (𝓝 μ)) ↔
      Tendsto (fun m ↦ expectedCovarianceSpectralMeasure (hX m)) atTop (𝓝 μ) := by
  refine ⟨tendsto_expectedCovarianceSpectralMeasure_of_ae_tendsto hX, fun hμ ↦ ?_⟩
  let C : Set ℝ := {x | ContinuousAt (cdf (μ : Measure ℝ)) x}
  have hC : Dense C := by
    simpa only [C, Set.compl_ofPred, not_not] using
      ((cdf (μ : Measure ℝ)).mono.countable_not_continuousAt).dense_compl ℝ
  obtain ⟨D, hDC, hDcount, hCD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace C).exists_countable_dense_subset
  have hD : Dense D := fun x ↦ closure_minimal hCD isClosed_closure (hC x)
  filter_upwards [(ae_ball_iff hDcount).2 (fun x _ ↦
    ae_tendsto_cdf_sampleCovariance_sub_expected hX hind hdim x)] with ω hω
  apply ProbabilityMeasure.tendsto_of_tendsto_cdf_of_dense hD
  intro x hx
  have hmean := ProbabilityMeasure.tendsto_cdf_of_tendsto_of_continuousAt hμ (hDC hx)
  simpa only [sub_add_cancel, zero_add] using (hω x hx).add hmean

end Sequence

end TauCeti.Probability
