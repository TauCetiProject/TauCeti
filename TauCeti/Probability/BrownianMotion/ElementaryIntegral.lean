/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.Moments
import Mathlib.Probability.Independence.Integration

/-!
# The elementary Brownian integral isometry

For Brownian increments relative to a filtration, a square-integrable coefficient known at the
left endpoint gives a square-integrable weighted increment. Distinct, chronologically disjoint
weighted increments are orthogonal, even though their coefficients need not be independent.
Consequently the second moment of their finite sum is the sum of their expected energies.
These are the finite-grid identities used to complete the elementary stochastic integral in L².

Only the filtered pre-Brownian laws are needed here: neither path regularity nor the usual
conditions on the filtration enter these moment calculations. Zero-length intervals are allowed.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- A weighted Brownian increment has mean zero when its measurable coefficient is known at
the left endpoint. -/
theorem integral_mul_sub (hB : IsFilteredPreBrownianReal ℱ B P) {s t : ℝ≥0} (hst : s ≤ t)
    {X : Ω → ℝ} (hX : Measurable[ℱ s] X) :
    ∫ ω, X ω * (B t ω - B s ω) ∂P = 0 := by
  have hlaw := hB.toIsPreBrownianReal.hasLaw_sub_of_le hst
  have h := (hB.indepFun_sub hst hX).symm.integral_fun_mul_eq_mul_integral
    (hX.mono (ℱ.le s) le_rfl).aestronglyMeasurable
    hlaw.aemeasurable.aestronglyMeasurable
  have hm : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    simpa only [Pi.sub_apply, integral_id_gaussianReal] using hlaw.integral_eq
  simpa only [Pi.sub_apply, hm, mul_zero] using h

/-- The second moment of a weighted Brownian increment is its expected energy. No integrability
hypothesis on the past-measurable coefficient is needed for this identity of totalized integrals. -/
theorem integral_sq_mul_sub (hB : IsFilteredPreBrownianReal ℱ B P) {s t : ℝ≥0} (hst : s ≤ t)
    {X : Ω → ℝ} (hX : Measurable[ℱ s] X) :
    ∫ ω, (X ω * (B t ω - B s ω)) ^ 2 ∂P =
      (∫ ω, X ω ^ 2 ∂P) * (↑t - ↑s) := by
  have hlaw := hB.toIsPreBrownianReal.hasLaw_sub_of_le hst
  have hind := (hB.indepFun_sub hst hX).symm.comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h := hind.integral_fun_mul_eq_mul_integral
    ((hX.mono (ℱ.le s) le_rfl).pow_const 2).aestronglyMeasurable
    ((hlaw.memLp (memLp_id_gaussianReal 2)).integrable_sq.aestronglyMeasurable)
  simp only [Function.comp_apply, id_eq, Pi.sub_apply] at h
  have hsecond : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (↑t - ↑s : ℝ) := by
    calc
      _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (t - s) := hlaw.integral_comp (by fun_prop)
      _ = (↑t - ↑s : ℝ) := by
        rw [integral_sq_gaussianReal]
        simp [NNReal.coe_sub hst]
  simpa only [mul_pow, hsecond] using h

/-- A square-integrable coefficient known at the left endpoint gives a square-integrable
weighted Brownian increment. -/
theorem memLp_mul_sub (hB : IsFilteredPreBrownianReal ℱ B P) {s t : ℝ≥0} (hst : s ≤ t)
    {X : Ω → ℝ} (hX : Measurable[ℱ s] X) (hXi : MemLp X 2 P) :
    MemLp (fun ω => X ω * (B t ω - B s ω)) 2 P := by
  have hlaw := hB.toIsPreBrownianReal.hasLaw_sub_of_le hst
  have hind := (hB.indepFun_sub hst hX).symm.comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  apply (memLp_two_iff_integrable_sq
    (hXi.aestronglyMeasurable.mul hlaw.aemeasurable.aestronglyMeasurable)).mpr
  simpa only [Pi.mul_def, Pi.sub_def, Function.comp_def, id_eq, mul_pow] using
    hind.integrable_mul hXi.integrable_sq (hlaw.memLp (memLp_id_gaussianReal 2)).integrable_sq

/-- Chronologically disjoint weighted Brownian increments are orthogonal. Their coefficients
may depend on the past and on one another. -/
theorem integral_mul_sub_mul_mul_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t u v : ℝ≥0} (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    {X Y : Ω → ℝ} (hX : Measurable[ℱ s] X) (hY : Measurable[ℱ u] Y) :
    ∫ ω, (X ω * (B t ω - B s ω)) * (Y ω * (B v ω - B u ω)) ∂P = 0 := by
  have hpast : Measurable[ℱ u] (fun ω => (X ω * (B t ω - B s ω)) * Y ω) :=
    ((hX.mono (ℱ.mono (hst.trans htu)) le_rfl).mul
      ((hB.adapted.measurable_le htu).sub
        (hB.adapted.measurable_le (hst.trans htu)))).mul hY
  simpa only [mul_assoc] using hB.integral_mul_sub huv hpast

/-- **Elementary Brownian integral isometry.** On any finite chronologically ordered family
of disjoint intervals, the second moment of the sum of weighted increments equals the sum of
the expected squared coefficients times the interval lengths. Each coefficient is known at
its own left endpoint and belongs to L². Empty families and zero-length intervals are allowed.
No independence between coefficients is assumed. -/
theorem integral_sq_sum_mul_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} [LinearOrder ι] (I : Finset ι) {s t : ι → ℝ≥0} {X : ι → Ω → ℝ}
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i < j → t i ≤ s j)
    (hX : ∀ i ∈ I, Measurable[ℱ (s i)] (X i)) (hXi : ∀ i ∈ I, MemLp (X i) 2 P) :
    ∫ ω, (∑ i ∈ I, X i ω * (B (t i) ω - B (s i) ω)) ^ 2 ∂P =
      ∑ i ∈ I, (∫ ω, X i ω ^ 2 ∂P) * (↑(t i) - ↑(s i)) := by
  have := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let U (i : ι) (ω : Ω) := X i ω * (B (t i) ω - B (s i) ω)
  have hU i (hi : i ∈ I) : MemLp (U i) 2 P :=
    hB.memLp_mul_sub (hst i hi) (hX i hi) (hXi i hi)
  have hmean i (hi : i ∈ I) : (∫ ω, U i ω ∂P) = 0 :=
    hB.integral_mul_sub (hst i hi) (hX i hi)
  have hcross i (hi : i ∈ I) j (hj : j ∈ I) (hij : i ≠ j) : cov[U i, U j; P] = 0 := by
    rw [covariance_eq_sub (hU i hi) (hU j hj), hmean i hi, hmean j hj, zero_mul, sub_zero]
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hB.integral_mul_sub_mul_mul_sub (hst i hi) (hdisj i hi j hj hij)
        (hst j hj) (hX i hi) (hX j hj)
    · simpa only [Pi.mul_def, mul_comm] using
        hB.integral_mul_sub_mul_mul_sub (hst j hj) (hdisj j hj i hi hij)
          (hst i hi) (hX j hj) (hX i hi)
  have hsum : MemLp (fun ω => ∑ i ∈ I, U i ω) 2 P := memLp_finsetSum I hU
  have hsum_mean : (∫ ω, ∑ i ∈ I, U i ω ∂P) = 0 := by
    rw [integral_finsetSum I (fun i hi => (hU i hi).integrable (by norm_num))]
    exact sum_eq_zero hmean
  have hv := variance_fun_sum' hU
  rw [variance_eq_integral hsum.aemeasurable, hsum_mean] at hv
  simp only [sub_zero] at hv
  rw [hv]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_eq_single_of_mem i hi (fun j hj hji => hcross i hi j hj hji.symm),
    covariance_self (hU i hi).aemeasurable,
    variance_eq_integral (hU i hi).aemeasurable, hmean i hi]
  simp only [sub_zero]
  exact hB.integral_sq_mul_sub (hst i hi) (hX i hi)

/-- The elementary Brownian isometry at an arbitrary observation time. Intervals after `T`
contribute zero and an interval straddling `T` contributes only its elapsed length. The
coefficients remain measurable at their original left endpoints; no measurability at an
earlier, truncated time is assumed. -/
theorem integral_sq_sum_mul_sub_min (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} [LinearOrder ι] (I : Finset ι) {s t : ι → ℝ≥0} {X : ι → Ω → ℝ}
    (hst : ∀ i ∈ I, s i ≤ t i)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i < j → t i ≤ s j)
    (hX : ∀ i ∈ I, Measurable[ℱ (s i)] (X i)) (hXi : ∀ i ∈ I, MemLp (X i) 2 P)
    (T : ℝ≥0) :
    ∫ ω, (∑ i ∈ I, X i ω * (B (min (t i) T) ω - B (min (s i) T) ω)) ^ 2 ∂P =
      ∑ i ∈ I, (∫ ω, X i ω ^ 2 ∂P) * (↑(min (t i) T) - ↑(min (s i) T)) := by
  classical
  -- Discard intervals not yet started before applying the terminal-grid theorem. Their
  -- coefficients need not be measurable at the observation time.
  have h := hB.integral_sq_sum_mul_sub (I.filter fun i => s i < T)
    (s := s) (t := fun i => min (t i) T) (X := X)
    (fun i hi => le_min (hst i (mem_filter.mp hi).1) (mem_filter.mp hi).2.le)
    (fun i hi j hj hij => (min_le_left _ _).trans
      (hdisj i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij))
    (fun i hi => hX i (mem_filter.mp hi).1)
    (fun i hi => hXi i (mem_filter.mp hi).1)
  have hsum (ω : Ω) :
      (∑ i ∈ I, X i ω * (B (min (t i) T) ω - B (min (s i) T) ω)) =
        ∑ i ∈ I.filter (fun i => s i < T), X i ω * (B (min (t i) T) ω - B (s i) ω) := by
    rw [sum_filter]
    refine sum_congr rfl fun i hi => ?_
    by_cases hs : s i < T
    · simp [hs, min_eq_left hs.le]
    · have hTs : T ≤ s i := le_of_not_gt hs
      simp [hs, min_eq_right hTs, min_eq_right (hTs.trans (hst i hi))]
  have henergy :
      (∑ i ∈ I, (∫ ω, X i ω ^ 2 ∂P) * (↑(min (t i) T) - ↑(min (s i) T))) =
        ∑ i ∈ I.filter (fun i => s i < T),
          (∫ ω, X i ω ^ 2 ∂P) * (↑(min (t i) T) - ↑(s i)) := by
    rw [sum_filter]
    refine sum_congr rfl fun i hi => ?_
    by_cases hs : s i < T
    · simp [hs, min_eq_left hs.le]
    · have hTs : T ≤ s i := le_of_not_gt hs
      simp [hs, min_eq_right hTs, min_eq_right (hTs.trans (hst i hi))]
  simp_rw [hsum, henergy]
  exact h

end TauCeti.Probability.IsFilteredPreBrownianReal
