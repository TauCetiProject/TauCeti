/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Covariance
public import TauCeti.Probability.RandomMatrix.SpectralMoment.Expected
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Probability.Moments.Variance
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Covariance, variance, and concentration of Wigner empirical spectral moments

For a Hermitian Wigner matrix `Hₙ₊₁`, the `k`-th moment of its empirical spectral measure embeds
into `ℂ` as `(n + 1)⁻¹ tr(Hₙ₊₁ ^ k)` (`Matrix.ofReal_integral_pow_spectralMeasure`). Combining this
identity with the connected two-trace covariance estimates in
`TauCeti.Probability.RandomMatrix.Covariance` yields `O((n + 1)⁻²)` bounds for all empirical
spectral moment covariances and variances under independent corner entries with centered
off-diagonal coordinates and uniformly bounded moments.

Since `(n + 1)⁻² → 0`, the `O((n + 1)⁻²)` variance bound yields Chebyshev concentration in
probability for all empirical spectral moment fluctuations around their expectations, including for
triangular arrays on varying probability spaces. Combined with the `O((n + 1)⁻¹/²)` expectation
bound for odd traces, every odd empirical spectral moment converges to zero in probability.
Almost-sure convergence on a fixed probability space via summability of `∑ (n + 1)⁻²` and the
Borel--Cantelli lemma is established in
`TauCeti.Probability.RandomMatrix.SpectralMoment.AlmostSure`.

## Main results

* `abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le` and
  `variance_integral_pow_spectralMeasure_wignerMatrix_le`: quantitative `O((n + 1)⁻²)` covariance
  and variance bounds for empirical spectral moments of all orders without diagonal centering.
* `measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge` and
  `tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability`: Chebyshev tail bound
  and convergence in probability of moment fluctuations to zero, allowing varying spaces.
* `tendsto_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix`: convergence to
  zero of expected odd empirical spectral moments under `(2m + 1)`-st moment assumptions alone,
  from the `O((n + 1)⁻¹/²)` bound
  `TauCeti.Probability.abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le`.
* `tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_probability`: convergence in
  probability of odd empirical spectral moments to zero, allowing varying spaces.

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

/-- **Empirical spectral moment covariance bound.** Under independent entries in the
`(n + 1) × (n + 1)` corner in `L^(k₁ + k₂)` with centered strictly upper coordinates and
`(k₁ + k₂)`-th absolute moments bounded by `B`, the covariance between the `k₁`-th and `k₂`-th
empirical spectral moments of `Hₙ₊₁` has absolute value at most
`2 * ((k₁ + k₂) / 2)^(k₁ + k₂) * B / (n + 1)²` for all `k₁, k₂, n : ℕ`. -/
theorem abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le {k₁ k₂ n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B) :
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
  have hbound := norm_integral_inv_mul_trace_pow_wignerMatrix_sub_mul_le
    hindep hξzero hξp hηp hξ hη
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcov]
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

/-- **Empirical spectral moment variance bound (AGZ Lemma 2.1.7).** Under independent entries in
the `(n + 1) × (n + 1)` corner in `L^(2k)` with centered strictly upper coordinates and `2k`-th
absolute moments bounded by `B`, the variance of the `k`-th empirical spectral moment of `Hₙ₊₁` is
at most `2 * k^(2k) * B / (n + 1)²` for every `k` and `n`. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  have := hindep.isProbabilityMeasure
  have hm := (memLp_integral_pow_spectralMeasure_wignerMatrix (p := 2) (fun _ ↦ inferInstance) n
    (fun ij hij ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hξp ij hij)
    (fun i hi ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hηp i hi)).aemeasurable
  have h2k : k + k = 2 * k := (two_mul k).symm
  have hdiv : (k + k) / 2 = k := by omega
  have hcov := abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le
    hindep hξzero (k₁ := k) (k₂ := k)
    (by simpa only [h2k] using hξp) (by simpa only [h2k] using hηp)
    (by simpa only [h2k] using hξ) (by simpa only [h2k] using hη)
  rw [hdiv, h2k] at hcov
  rw [← covariance_self hm]
  exact (le_abs_self _).trans hcov

/-- **Chebyshev tail bound for empirical spectral moments.** Under independent entries in the
`(n + 1) × (n + 1)` corner in `L^(2k)` with centered strictly upper coordinates and `2k`-th
absolute moments bounded by `B`, the probability that the `k`-th empirical spectral moment of
`Hₙ₊₁` deviates from its expectation by at least `ε > 0` is bounded by
`2 * k^(2k) * B / (n + 1)² / ε²`. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have := hindep.isProbabilityMeasure
  have hmem := memLp_integral_pow_spectralMeasure_wignerMatrix (p := 2) (fun _ ↦ inferInstance) n
    (fun ij hij ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hξp ij hij)
    (fun i hi ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hηp i hi)
  have hvar := variance_integral_pow_spectralMeasure_wignerMatrix_le hindep hξzero hξp hηp hξ hη
  exact (meas_ge_le_variance_div_sq hmem hε).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg ε)))

end FixedSpace

section VaryingSpaces

/-- Every expected odd empirical spectral moment of a Wigner matrix converges to zero under
independent corner entries in `L^(2m + 1)` with centered strictly upper coordinates and uniformly
bounded `(2m + 1)`-st absolute moments, including for triangular arrays on varying probability
spaces. -/
theorem tendsto_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {m : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (2 * m + 1 : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (2 * m + 1 : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * m + 1) ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * m + 1) ∂P n ≤ B) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ (2 * m + 1)
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  exact squeeze_zero_norm (fun n ↦ by
    simpa only [Real.norm_eq_abs] using
      abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
        (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n)) hlim

/-- Empirical spectral moment fluctuations around their expectations vanish in probability under
independent corner entries in `L^(2k)` with centered strictly upper coordinates and uniformly
bounded `2k`-th absolute moments, including for triangular arrays on varying probability spaces. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n|})
      atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hmem (n : ℕ) : MemLp (fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) 2 (P n) :=
    memLp_integral_pow_spectralMeasure_wignerMatrix (p := 2) (fun _ ↦ inferInstance) n
      (fun ij hij ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hξp n ij hij)
      (fun i hi ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hηp n i hi)
  have hvar : Tendsto (fun n ↦ Var[fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ); P n]) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ variance_nonneg _ _)
      (fun n ↦ variance_integral_pow_spectralMeasure_wignerMatrix_le
        (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n))
      (by
        simpa using tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop two_ne_zero).comp
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)))
  exact tendsto_measure_abs_sub_integral_ge_of_tendsto_variance hmem hvar hε

/-- Every odd empirical spectral moment of a Wigner matrix converges to zero in probability under
independent corner entries in `L^(4m + 2)` with centered strictly upper coordinates and uniformly
bounded `(4m + 2)`-th absolute moments, including for triangular arrays on varying probability
spaces. -/
theorem tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {m : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 →
      MemLp (ξ n ij) (2 * (2 * m + 1) : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (2 * (2 * m + 1) : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 →
      ∫ ω, ‖ξ n ij ω‖ ^ (2 * (2 * m + 1)) ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * (2 * m + 1)) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |∫ x, x ^ (2 * m + 1) ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)|})
      atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  let M (n : ℕ) (ω : Ω n) : ℝ :=
    ∫ x, x ^ (2 * m + 1) ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)
  have hle : ((2 * m + 1 : ℕ) : ℝ≥0∞) ≤ (2 * (2 * m + 1) : ℕ) := by exact_mod_cast (by omega)
  have hmean : Tendsto (fun n ↦ |∫ ω', M n ω' ∂P n|) atTop (𝓝 0) := by
    simpa only [abs_zero] using
      (tendsto_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
        hindep hξzero (fun n ij hij ↦ (hξp n ij hij).mono_exponent hle)
        (fun n i hi ↦ (hηp n i hi).mono_exponent hle)
        (fun n ij hij ↦ ((hξp n ij hij).integrable_norm_pow'
          |>.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul prob_le_one).trans
            (Real.sqrt_le_sqrt (hξ n ij hij)))
        (fun n i hi ↦ ((hηp n i hi).integrable_norm_pow'
          |>.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul prob_le_one).trans
            (Real.sqrt_le_sqrt (hη n i hi)))).abs
  have hev : ∀ᶠ n in atTop,
      P n {ω | ε ≤ |M n ω|} ≤ P n {ω | ε / 2 ≤ |M n ω - ∫ ω', M n ω' ∂P n|} := by
    filter_upwards [hmean.eventually (gt_mem_nhds (half_pos hε))] with n hn
    refine measure_mono fun ω hω ↦ ?_
    have htri := abs_sub_abs_le_abs_sub (M n ω) (∫ ω', M n ω' ∂P n)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
      hindep hξzero hξp hηp hξ hη (half_pos hε))
    (.of_forall fun _ ↦ bot_le) hev

end VaryingSpaces

end TauCeti.Probability
