/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Covariance
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.Moments.Variance

/-!
# Covariance, variance, and concentration of Wigner empirical spectral moments

For a Hermitian Wigner matrix `Hₙ₊₁`, the `k`-th moment of its empirical spectral measure embeds
into `ℂ` as `(n + 1)⁻¹ tr(Hₙ₊₁ ^ k)` (`Matrix.ofReal_integral_pow_spectralMeasure`). Combining this
identity with the connected two-trace covariance estimates in
`TauCeti.Probability.RandomMatrix.Covariance` yields `O(n⁻²)` bounds for all empirical spectral
moment covariances and variances under independent centered entries with uniformly bounded moments.

Summability of `∑ (n + 1)⁻²` then gives Chebyshev concentration in probability (including for
triangular arrays on varying probability spaces) and Borel–Cantelli almost-sure vanishing of all
empirical spectral moment fluctuations around their expectations. Combined with the `O(n⁻¹/²)`
expectation bound for odd traces, every odd empirical spectral moment converges to zero in
probability and almost surely.

## Main results

* `memLp_two_integral_pow_spectralMeasure_wignerMatrix`: the `k`-th empirical spectral moment of
  `Hₙ₊₁` lies in `L²` under `L^(2k)` entries.
* `abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le` and
  `variance_integral_pow_spectralMeasure_wignerMatrix_le`: quantitative `O((n + 1)⁻²)` covariance
  and variance bounds for empirical spectral moments of all orders.
* `measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge` and
  `tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability`: Chebyshev tail bound
  and convergence in probability of moment fluctuations to zero, allowing varying spaces.
* `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean` and
  `ae_forall_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean`: almost-sure vanishing of
  empirical spectral moment fluctuations via Borel–Cantelli.
* `ae_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix`,
  `ae_forall_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix`, and
  `tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_probability`: almost-sure and
  in-probability convergence of odd empirical spectral moments to zero.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.4, Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.4.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology ENNReal

namespace TauCeti.Probability

section FixedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- If the entries of the Wigner array lie in `L^(2k)` on a finite measure space, the `k`-th
empirical spectral moment of `Hₙ₊₁` lies in `L²` for every `k` and `n`, without independence or
centering. -/
theorem memLp_two_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P := by
  simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin]
  exact (memLp_two_trace_pow_wignerMatrix hξp hηp (n + 1)).re.const_mul _

/-- **Empirical spectral moment covariance bound.** On a probability space, under independent
centered entries in `L^(k₁ + k₂)` with `(k₁ + k₂)`-th absolute moments bounded by `B`, the
covariance between the `k₁`-th and `k₂`-th empirical spectral moments of `Hₙ₊₁` has absolute value
at most `2 * ((k₁ + k₂) / 2)^(k₁ + k₂) * B / (n + 1)²` for all `k₁, k₂, n : ℕ`. -/
theorem abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k₁ k₂ : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B) (n : ℕ) :
    |cov[fun ω ↦ ∫ x, x ^ k₁ ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ),
      fun ω ↦ ∫ x, x ^ k₂ ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P]| ≤
      2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n + 1 : ℝ) ^ 2 := by
  have hmom (k : ℕ) (ω : Ω) :
      (((∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) : ℝ) : ℂ) =
        ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace := by
    simpa [Fintype.card_fin] using Matrix.ofReal_integral_pow_spectralMeasure (𝕜 := ℂ)
      (wignerMatrix ξ η (n + 1) ω) (wignerMatrix_isHermitian ξ η ω (n + 1)) k
  set M₁ : Ω → ℝ := fun ω ↦ ∫ x, x ^ k₁ ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)
  set M₂ : Ω → ℝ := fun ω ↦ ∫ x, x ^ k₂ ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)
  have hmean₁ : ((∫ ω', M₁ ω' ∂P : ℝ) : ℂ) =
      ∫ ω', ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω' ^ k₁).trace ∂P := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun ω' ↦ hmom k₁ ω')
  have hmean₂ : ((∫ ω', M₂ ω' ∂P : ℝ) : ℂ) =
      ∫ ω', ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω' ^ k₂).trace ∂P := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun ω' ↦ hmom k₂ ω')
  have hcov : ((cov[M₁, M₂; P] : ℝ) : ℂ) =
      ∫ ω, ((((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k₁).trace -
          ∫ ω', ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω' ^ k₁).trace ∂P) *
        (((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k₂).trace -
          ∫ ω', ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω' ^ k₂).trace ∂P)) ∂P := by
    rw [covariance, ← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, hmean₁, hmean₂, M₁, M₂, hmom]
  have hbound := norm_integral_centered_trace_pow_mul_wignerMatrix_le
    hindep hξzero hηzero (n := n + 1) hξp hηp hξ hη
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcov]
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

/-- **Empirical spectral moment variance bound (AGZ Lemma 2.1.7).** On a probability space, under
independent centered entries in `L^(2k)` with `2k`-th absolute moments bounded by `B`, the variance
of the `k`-th empirical spectral moment of `Hₙ₊₁` is at most `2 * k^(2k) * B / (n + 1)²` for every
`k` and `n`. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) (n : ℕ) :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  have hm := (memLp_two_integral_pow_spectralMeasure_wignerMatrix hξp hηp n).aemeasurable
  have h2k : k + k = 2 * k := (two_mul k).symm
  have hdiv : (k + k) / 2 = k := by omega
  have hcov := abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le
    hindep hξzero hηzero (k₁ := k) (k₂ := k)
    (by simpa only [h2k] using hξp) (by simpa only [h2k] using hηp)
    (by simpa only [h2k] using hξ) (by simpa only [h2k] using hη) n
  rw [hdiv, h2k] at hcov
  rw [← covariance_self hm]
  exact (le_abs_self _).trans hcov

/-- **Chebyshev tail bound for empirical spectral moments.** On a probability space, under
independent centered entries in `L^(2k)` with `2k`-th absolute moments bounded by `B`, the
probability that the `k`-th empirical spectral moment of `Hₙ₊₁` deviates from its expectation by at
least `ε > 0` is bounded by `2 * k^(2k) * B / (n + 1)² / ε²`. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have hmem := memLp_two_integral_pow_spectralMeasure_wignerMatrix hξp hηp n
  have hvar := variance_integral_pow_spectralMeasure_wignerMatrix_le
    hindep hξzero hηzero hξp hηp hξ hη n
  exact (meas_ge_le_variance_div_sq hmem hε).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg ε)))

/-- **Almost-sure vanishing of empirical spectral moment fluctuations.** On a probability space, if
the entries of the Wigner array are independent, centered, in `L^(2k)`, and have `2k`-th absolute
moments uniformly bounded by `B`, then the `k`-th empirical spectral moment minus its expectation
converges almost surely to zero as `n → ∞`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {k : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) := by
  let X : ℕ → Ω → ℝ := fun n ω ↦
    (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
    ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
      (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P
  have hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, inv_pow] using
      (summable_nat_add_iff 1).2
        ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))
  set C : ℝ := 2 * (k : ℝ) ^ (2 * k) * B
  have hbc (m : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |X n ω| < (m + 1 : ℝ)⁻¹ := by
    have hbound (n : ℕ) : P {ω | (m + 1 : ℝ)⁻¹ ≤ |X n ω|} ≤
        ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) :=
      measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
        hindep hξzero hηzero hξp hηp hξ hη n (inv_pos.mpr (by positivity))
    have hsum : Summable (fun n : ℕ ↦ (C / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) := by
      have ht := Summable.mul_right ((((m + 1 : ℝ)⁻¹) ^ 2)⁻¹) (Summable.mul_left C hs)
      simpa only [div_eq_mul_inv, inv_pow, mul_assoc] using ht
    have hfinite : (∑' n, P {ω | (m + 1 : ℝ)⁻¹ ≤ |X n ω|}) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum hbound)
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfinite
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω m] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn.trans (by simpa only [one_div] using hm)

/-- **Simultaneous almost-sure vanishing of all empirical spectral moment fluctuations.** When every
even moment order `2k` of the independent centered entries is uniformly bounded across the array by
`B k`, on a single full-measure event the fluctuations of all empirical spectral moments around
their expectations vanish as `n → ∞`. -/
theorem ae_forall_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {B : ℕ → ℝ}
    (hξp : ∀ k ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ k i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ k ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B k)
    (hη : ∀ k i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B k) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n ↦
      (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) :=
  ae_all_iff.2 fun k ↦ ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    hindep hξzero hηzero (hξp k) (hηp k) (hξ k) (hη k)

private theorem abs_integral_odd_spectralMeasure_wignerMatrix_le [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {m : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * (2 * m + 1) : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * (2 * m + 1) : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * (2 * m + 1)) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * (2 * m + 1)) ∂P ≤ B) (n : ℕ) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * √B / Real.sqrt (n + 1 : ℝ) := by
  set r := 2 * m + 1
  have hle : ((r : ℕ) : ℝ≥0∞) ≤ (2 * r : ℕ) := by exact_mod_cast (by omega)
  have hsq {E : Type} [NormedAddCommGroup E] {f : Ω → E}
      (hfp : MemLp f (2 * r : ℕ) P) (hf : ∫ ω, ‖f ω‖ ^ (2 * r) ∂P ≤ B) :
      ∫ ω, ‖f ω‖ ^ r ∂P ≤ √B := by
    have hg : MemLp (fun ω ↦ ‖f ω‖ ^ r) 2 P :=
      (memLp_two_iff_integrable_sq_norm (hfp.aestronglyMeasurable.norm.pow r)).2 <|
        (hfp.integrable_norm_pow (by positivity)).congr (.of_forall fun ω ↦ by
          dsimp only [Pi.pow_apply]
          rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _), ← pow_mul, mul_comm])
    exact (integral_le_sqrt_integral_sq hg).trans <| Real.sqrt_le_sqrt <|
      (le_of_eq (integral_congr_ae (.of_forall fun ω ↦ by rw [← pow_mul, mul_comm]))).trans hf
  have hmean : ((∫ ω, (∫ x, x ^ r ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P : ℝ) : ℂ) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ r).trace ∂P := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    simpa [Fintype.card_fin] using Matrix.ofReal_integral_pow_spectralMeasure (𝕜 := ℂ)
      (wignerMatrix ξ η (n + 1) ω) (wignerMatrix_isHermitian ξ η ω (n + 1)) r
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hmean]
  simpa only [Nat.cast_add, Nat.cast_one] using
    norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le hindep hξzero hηzero
      (n := n + 1) (fun ij ↦ (hξp ij).mono_exponent hle) (fun i ↦ (hηp i).mono_exponent hle)
      (fun ij ↦ hsq (hξp ij) (hξ ij)) (fun i ↦ hsq (hηp i) (hη i))

/-- **Almost-sure convergence of odd empirical spectral moments to zero.** On a probability space,
under independent centered entries in `L^(4m + 2)` with `(4m + 2)`-th absolute moments uniformly
bounded by `B`, the `(2m + 1)`-st empirical spectral moment of `Hₙ₊₁` converges almost surely to
zero as `n → ∞`. -/
theorem ae_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
    [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {m : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * (2 * m + 1) : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * (2 * m + 1) : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * (2 * m + 1)) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * (2 * m + 1)) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦
      (m + 1 : ℝ) ^ (2 * m + 1) * √B / Real.sqrt (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hmean : Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ (2 * m + 1)
      ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ by
      simpa only [Real.norm_eq_abs] using
        abs_integral_odd_spectralMeasure_wignerMatrix_le
          hindep hξzero hηzero hξp hηp hξ hη n) hlim
  filter_upwards [ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    hindep hξzero hηzero hξp hηp hξ hη] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hmean

/-- **Simultaneous almost-sure convergence of all odd empirical spectral moments to zero.** When
every `(4m + 2)`-th absolute moment of the independent centered entries is uniformly bounded by
`B m`, on a single full-measure event all odd empirical spectral moments converge to zero. -/
theorem ae_forall_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
    [IsProbabilityMeasure P]
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    {B : ℕ → ℝ}
    (hξp : ∀ m ij, MemLp (ξ ij) (2 * (2 * m + 1) : ℕ) P)
    (hηp : ∀ m i, MemLp (η i) (2 * (2 * m + 1) : ℕ) P)
    (hξ : ∀ m ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * (2 * m + 1)) ∂P ≤ B m)
    (hη : ∀ m i, ∫ ω, ‖η i ω‖ ^ (2 * (2 * m + 1)) ∂P ≤ B m) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, Tendsto (fun n ↦
      ∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 0) :=
  ae_all_iff.2 fun m ↦ ae_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
    hindep hξzero hηzero (hξp m) (hηp m) (hξ m) (hη m)

end FixedSpace

section VaryingSpaces

/-- Empirical spectral moment fluctuations around their expectations vanish in probability under
uniformly bounded `2k`-th absolute moments, including for triangular arrays on varying probability
spaces. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n|})
      atTop (𝓝 0) := by
  set C : ℝ := 2 * (k : ℝ) ^ (2 * k) * B
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreal : Tendsto (fun n : ℕ ↦ (C / (n + 1 : ℝ) ^ 2) / ε ^ 2) atTop (𝓝 0) := by
    convert ((hinv.pow 2).const_mul C).div_const (ε ^ 2) using 1
    · ext n
      simp [div_eq_mul_inv, inv_pow]
    · simp
  have hbound : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((C / (n + 1 : ℝ) ^ 2) / ε ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ bot_le) (fun n ↦
      measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
        (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) n hε)

/-- Every odd empirical spectral moment of a Wigner matrix converges to zero in probability under
independent centered entries with uniformly bounded `(4m + 2)`-th absolute moments, including for
triangular arrays on varying probability spaces. -/
theorem tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {m : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * (2 * m + 1) : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * (2 * m + 1) : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * (2 * m + 1)) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * (2 * m + 1)) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |∫ x, x ^ (2 * m + 1) ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)|})
      atTop (𝓝 0) := by
  let M (n : ℕ) (ω : Ω n) : ℝ :=
    ∫ x, x ^ (2 * m + 1) ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)
  have hlim : Tendsto (fun n : ℕ ↦
      (m + 1 : ℝ) ^ (2 * m + 1) * √B / Real.sqrt (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hmean : Tendsto (fun n ↦ |∫ ω', M n ω' ∂P n|) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ abs_nonneg _)
      (fun n ↦ abs_integral_odd_spectralMeasure_wignerMatrix_le
        (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) n) hlim
  have hev : ∀ᶠ n in atTop,
      P n {ω | ε ≤ |M n ω|} ≤ P n {ω | ε / 2 ≤ |M n ω - ∫ ω', M n ω' ∂P n|} := by
    filter_upwards [hmean.eventually (gt_mem_nhds (half_pos hε))] with n hn
    refine measure_mono fun ω hω ↦ ?_
    have htri := abs_sub_abs_le_abs_sub (M n ω) (∫ ω', M n ω' ∂P n)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
      hindep hξzero hηzero hξp hηp hξ hη (half_pos hε))
    (.of_forall fun _ ↦ bot_le) hev

end VaryingSpaces

end TauCeti.Probability
