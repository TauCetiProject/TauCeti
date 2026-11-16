/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.WeakConvergence
public import TauCeti.Probability.RandomMatrix.SpectralMoment.Expected
public import TauCeti.Probability.RandomMatrix.SpectralMoment.Variance
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.MeasureTheory.Function.L1Space.Integrable

/-!
# Moment convergence and the moment-method semicircle law for Wigner matrices

Combining the expected-moment limit
(`TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix_array`),
the summable `O_k((n + 1)⁻²)` variance bound
(`TauCeti.Probability.measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge`), and the
method of moments on `ℝ` (`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow`)
yields Wigner's semicircle law for ensembles with uniformly bounded moments of all orders:

* for triangular Wigner arrays `(Ω n, P n, ξ n, η n)` on varying probability spaces with independent
  centered entries, unit off-diagonal second absolute moments, and uniformly bounded `2 * k`-th
  absolute moments, the `k`-th empirical spectral moment converges in probability to
  `∫ x, x ^ k ∂semicircleReal 0 1`;
* for a single infinite Wigner array on `(Ω, P)`, Borel–Cantelli turns the `O_k((n + 1)⁻²)` tail
  bound into almost-sure convergence of the `k`-th empirical spectral moment to its mean (without
  requiring unit variance) and hence to `∫ x, x ^ k ∂semicircleReal 0 1` when off-diagonal second
  moments equal `1`;
* intersecting the full-measure events across all `k : ℕ` and invoking the method of moments against
  the compactly supported limit `semicircleReal 0 1` shows that the empirical spectral measures
  `(wignerMatrix ξ η (n + 1) ω).spectralMeasure _` converge weakly to `semicircleReal 0 1` almost
  surely.

Because `x ^ k ≤ x ^ (2 * k) + 1` for `0 ≤ x`, a uniform `2 * k`-th moment bound on a probability
space automatically controls the `k`-th absolute moments needed for the expected-moment limit, so
none of the theorems below require separate `k`-th moment hypotheses.

## Main results

* `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix_probability`: convergence
  in probability of the `k`-th empirical spectral moment to `∫ x, x ^ k ∂semicircleReal 0 1` for
  triangular Wigner arrays.
* `TauCeti.Probability.ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean`: almost-sure
  vanishing of fluctuations of the `k`-th empirical spectral moment around its mean.
* `TauCeti.Probability.ae_tendsto_integral_pow_spectralMeasure_wignerMatrix`: almost-sure
  convergence of the `k`-th empirical spectral moment to `∫ x, x ^ k ∂semicircleReal 0 1`.
* `TauCeti.Probability.ae_tendsto_spectralMeasure_wignerMatrix`: almost-sure weak convergence of
  the empirical spectral measures of Wigner matrices with uniformly bounded moments of all orders to
  `semicircleReal 0 1`.

## References

* E. P. Wigner, *Characteristic vectors of bordered matrices with infinite dimensions*, Ann. of
  Math. (2) **62** (1955), 548–564.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Theorem 2.1.1 and §2.1.3.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter Set
open TauCeti
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

private theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_array_of_two_mul
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    (k : ℕ) {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun j : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) j) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0) (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∫ x, x ^ k
        ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have hξpk (n : ℕ) (ij : StrictUpper) : MemLp (ξ n ij) k (P n) :=
    (hξp n ij).mono_exponent (by norm_cast; omega)
  have hηpk (n i : ℕ) : MemLp (η n i) k (P n) :=
    (hηp n i).mono_exponent (by norm_cast; omega)
  have hξk (n : ℕ) (ij : StrictUpper) : ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B + 1 := by
    have h := (hξp n ij).integral_norm_pow_le_add_measureReal_univ
      (Nat.le_mul_of_pos_left k two_pos)
    rw [probReal_univ] at h
    exact h.trans (add_le_add_left (hξ n ij) 1)
  have hηk (n i : ℕ) : ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B + 1 := by
    have h := (hηp n i).integral_norm_pow_le_add_measureReal_univ
      (Nat.le_mul_of_pos_left k two_pos)
    rw [probReal_univ] at h
    exact h.trans (add_le_add_left (hη n i) 1)
  exact tendsto_integral_pow_spectralMeasure_wignerMatrix_array k hindep hξzero hηzero hsecond
    hξpk hηpk hξk hηk

/-- **Convergence in probability of Wigner spectral moments for triangular arrays.** For independent
centered entries on varying probability spaces with unit off-diagonal second absolute moments and
uniformly bounded `2 * k`-th absolute moments, the `k`-th empirical spectral moment of `Hₙ₊₁`
converges in probability to `∫ x, x ^ k ∂semicircleReal 0 1`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    (k : ℕ) {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun j : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) j) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0) (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
        |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
            (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
          ∫ x, x ^ k ∂semicircleReal 0 1|})
      atTop (𝓝 0) := by
  let X (n : ℕ) (ω : Ω n) : ℝ :=
    ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)
  let m : ℝ := ∫ x, x ^ k ∂semicircleReal 0 1
  have hmean := tendsto_integral_pow_spectralMeasure_wignerMatrix_array_of_two_mul k hindep
    hξzero hηzero hsecond hξp hηp hξ hη
  have hfluc := tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability k hindep
    hξzero hηzero hξp hηp hξ hη (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [Metric.tendsto_nhds.mp hmean (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq] at hn
  refine measure_mono fun ω hω ↦ ?_
  simp only [mem_ofPred_eq] at hω ⊢
  linarith [abs_sub_le (X n ω) (∫ ω', X n ω' ∂P n) m]

section FixedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Fluctuations of the `k`-th empirical spectral moment of `Hₙ₊₁` around its mean tend to zero
almost surely when the Wigner array has independent centered entries and uniformly bounded
`2 * k`-th absolute moments. No unit-variance assumption on the entries is needed. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean (k : ℕ) {B : ℝ}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
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
      (summable_nat_add_iff 1).2 ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))
  have hbc (m : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |X n ω| < (m + 1 : ℝ)⁻¹ := by
    have hbound (n : ℕ) : P {ω | (m + 1 : ℝ)⁻¹ ≤ |X n ω|} ≤
        ENNReal.ofReal
          ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) :=
      measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge k n hindep hξzero hηzero
        hξp hηp hξ hη (inv_pos.mpr (by positivity))
    have hsum : Summable (fun n : ℕ ↦
        (2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) := by
      have ht := Summable.mul_right ((((m + 1 : ℝ)⁻¹) ^ 2)⁻¹)
        (Summable.mul_left (2 * (k : ℝ) ^ (2 * k) * B) hs)
      simpa only [div_eq_mul_inv, inv_pow, mul_assoc] using ht
    have hfinite : (∑' n, P {ω | (m + 1 : ℝ)⁻¹ ≤ |X n ω|}) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum hbound)
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfinite
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω m] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn.trans (by simpa only [one_div] using hm)

/-- **Almost-sure convergence of Wigner empirical spectral moments.** For independent centered
entries with unit off-diagonal second absolute moments and uniformly bounded `2 * k`-th absolute
moments, the `k`-th empirical spectral moment of `Hₙ₊₁` converges almost surely to
`∫ x, x ^ k ∂semicircleReal 0 1`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix (k : ℕ) {B : ℝ}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have hm := tendsto_integral_pow_spectralMeasure_wignerMatrix_array_of_two_mul k
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hηzero) (fun _ ↦ hsecond)
    (fun _ ↦ hξp) (fun _ ↦ hηp) (fun _ ↦ hξ) (fun _ ↦ hη)
  filter_upwards [ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean k hindep
    hξzero hηzero hξp hηp hξ hη] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hm

/-- **Wigner's semicircle law via the method of moments.** Let `(ξ, η)` be an infinite Wigner array
of independent centered entries on a probability space `(Ω, P)` with unit off-diagonal second
absolute moments and, for every `k : ℕ`, a uniform bound on the `2 * k`-th absolute moments across
all array positions. Then almost surely the empirical spectral measures of
`wignerMatrix ξ η (n + 1)` converge weakly to the standard semicircle law `semicircleReal 0 1`. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ k ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ k i, MemLp (η i) (2 * k : ℕ) P)
    (hmom : ∀ k, ∃ B, (∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) ∧
      (∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)))
      atTop (𝓝 (⟨semicircleReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
    refine ae_all_iff.mpr fun k ↦ ?_
    obtain ⟨B, hξ, hη⟩ := hmom k
    exact ae_tendsto_integral_pow_spectralMeasure_wignerMatrix k hindep hξzero hηzero hsecond
      (hξp k) (hηp k) hξ hη
  have hsupp : ((⟨semicircleReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)
      (Icc (0 - 2 * Real.sqrt (1 : ℝ≥0)) (0 + 2 * Real.sqrt (1 : ℝ≥0)))ᶜ = 0 := by
    simpa only [ProbabilityMeasure.coe_mk, compl_def, mem_ofPred_eq] using
      ae_iff.mp (ae_mem_Icc_semicircleReal 0 1)
  filter_upwards [hall] with ω hω
  refine MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow isCompact_Icc hsupp
    (fun k ↦ Eventually.of_forall fun n ↦ ?_) fun k ↦ ?_
  · rw [Matrix.spectralMeasure_def, empiricalMeasureOfFintype_toMeasure,
      integrable_finsetSum_measure]
    exact fun i _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)
  · simpa only [ProbabilityMeasure.coe_mk] using hω k

end FixedSpace

end TauCeti.Probability
