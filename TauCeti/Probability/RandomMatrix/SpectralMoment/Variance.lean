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
import TauCeti.Probability.Independence.Basic

/-!
# Covariance, variance, and concentration of Wigner empirical spectral moments

For a Hermitian Wigner matrix `Hₙ₊₁`, the `k`-th moment of its empirical spectral measure embeds
into `ℂ` as `(n + 1)⁻¹ tr(Hₙ₊₁ ^ k)` (`Matrix.ofReal_integral_pow_spectralMeasure`). Combining this
identity with the connected two-trace covariance estimates in
`TauCeti.Probability.RandomMatrix.Covariance` via zero-padding outside each `(n + 1) × (n + 1)`
corner yields `O((n + 1)⁻²)` bounds for all empirical spectral moment covariances and variances
under corner-local independent centered entries with uniformly bounded moments.

Since `(n + 1)⁻² → 0`, the `O((n + 1)⁻²)` variance bound yields Chebyshev concentration in
probability for all empirical spectral moment fluctuations around their expectations, including for
triangular arrays on varying probability spaces. Combined with the `O((n + 1)⁻¹/²)` expectation
bound for odd traces, every odd empirical spectral moment converges to zero in probability; combined
with the general expected-moment convergence in
`TauCeti.Probability.RandomMatrix.SpectralMoment.Expected`, every `k`-th empirical spectral moment
converges in probability to the `k`-th moment of `semicircleReal 0 s` when both diagonal and
strictly upper-triangular entry families lie in `L^(2k)` in each corner with uniformly bounded
`2k`-th absolute moment integrals, while the strictly upper-triangular entries have common second
absolute moment `s` across all corners.
Almost-sure convergence on a fixed probability space via summability of `∑ (n + 1)⁻²` and the
Borel--Cantelli lemma is established in
`TauCeti.Probability.RandomMatrix.SpectralMoment.AlmostSure`.

## Main results

* `abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le` and
  `variance_integral_pow_spectralMeasure_wignerMatrix_le`: quantitative `O((n + 1)⁻²)` covariance
  and variance bounds for empirical spectral moments of all orders under corner-local hypotheses.
* `measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge` and
  `tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability`: Chebyshev tail bound
  and convergence in probability of moment fluctuations to zero, allowing varying spaces.
* `tendsto_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix`: convergence to
  zero of expected odd empirical spectral moments under `(2m + 1)`-st moment assumptions alone,
  from the `O((n + 1)⁻¹/²)` bound
  `TauCeti.Probability.abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le`.
* `tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_probability`: convergence in
  probability of odd empirical spectral moments to zero, allowing varying spaces.
* `tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability`: convergence in
  probability of the `k`-th empirical spectral moment to `∫ x, x ^ k ∂semicircleReal 0 s` when
  both entry families lie in `L^(2k)` in each corner with uniformly bounded `2k`-th absolute moment
  integrals and the strictly upper-triangular entries have common second absolute moment `s`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.4, Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.4.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

section CornerHelpers

open Classical in
private theorem iIndepFun_ite_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P) :
    iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (fun ij ↦ if ij.val.2 < n then ξ ij else 0)
        (fun i ω ↦ ((if i < n then η i else 0) ω : ℂ)) idx) P := by
  have := hindep.isProbabilityMeasure
  let s : Set (StrictUpper ⊕ ℕ) := {idx | Sum.elim (fun ij ↦ ij.val.2 < n) (fun i ↦ i < n) idx}
  refine ProbabilityTheory.iIndepFun.of_subtype_of_ae_eq_const_outside (s := s) ?_ ?_
  · refine (hindep.precomp (Equiv.subtypeSum (p := fun idx ↦ idx ∈ s)).injective).congr
      fun ⟨idx, hidx⟩ ↦ .of_forall fun ω ↦ ?_
    rcases idx with ij | i <;> simp only [s, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] at hidx
    · change ξ ij ω = (if ij.val.2 < n then ξ ij else 0) ω
      simp [hidx]
    · change (η i ω : ℂ) = ((if i < n then η i else 0) ω : ℂ)
      simp [hidx]
  · intro idx hnot
    refine ⟨0, .of_forall fun ω ↦ ?_⟩
    rcases idx with ij | i <;> simp only [s, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] at hnot
    · change (if ij.val.2 < n then ξ ij else 0) ω = 0
      simp [hnot]
    · change ((if i < n then η i else 0) ω : ℂ) = 0
      simp [hnot]

private theorem ite_zero_memLp_moment {ι Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ι → Prop) [DecidablePred p]
    {f : ι → Ω → E} {k : ℕ} {B : ℝ}
    (h0B : ∫ _ω : Ω, (0 : ℝ) ^ k ∂P ≤ B)
    (hf : ∀ i, p i → ∫ ω, f i ω ∂P = 0 ∧ MemLp (f i) (k : ℕ) P ∧ ∫ ω, ‖f i ω‖ ^ k ∂P ≤ B) :
    (∀ i, ∫ ω, (if p i then f i else 0) ω ∂P = 0) ∧
      (∀ i, MemLp (if p i then f i else 0) (k : ℕ) P) ∧
      (∀ i, ∫ ω, ‖(if p i then f i else 0) ω‖ ^ k ∂P ≤ B) := by
  have h (i : ι) : ∫ ω, (if p i then f i else 0) ω ∂P = 0 ∧
      MemLp (if p i then f i else 0) (k : ℕ) P ∧
      ∫ ω, ‖(if p i then f i else 0) ω‖ ^ k ∂P ≤ B := by
    by_cases hi : p i
    · simp only [hi, ↓reduceIte]
      exact hf i hi
    · simp only [hi, ↓reduceIte, Pi.zero_apply, integral_zero, MemLp.zero, norm_zero, true_and]
      exact h0B
  exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2.1, fun i ↦ (h i).2.2⟩

end CornerHelpers

section FixedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

private theorem abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le_global
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
  have hbound := norm_integral_inv_mul_trace_pow_wignerMatrix_sub_mul_le
    hindep hξzero hηzero (n := n + 1) hξp hηp hξ hη
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcov]
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

/-- **Empirical spectral moment covariance bound.** Under corner-local independent centered entries
in `L^(k₁ + k₂)` with `(k₁ + k₂)`-th absolute moments bounded by `B`, the covariance between the
`k₁`-th and `k₂`-th empirical spectral moments of `Hₙ₊₁` has absolute value at most
`2 * ⌊(k₁ + k₂) / 2⌋^(k₁ + k₂) * B / (n + 1)²` (where `⌊(k₁ + k₂) / 2⌋` is the `ℕ`-division
`(k₁ + k₂) / 2`) for all `k₁, k₂, n : ℕ`. -/
theorem abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le
    {k₁ k₂ n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n + 1, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (k₁ + k₂ : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (k₁ + k₂ : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (k₁ + k₂) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (k₁ + k₂) ∂P ≤ B) :
    |cov[fun ω ↦ ∫ x, x ^ k₁ ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ),
      fun ω ↦ ∫ x, x ^ k₂ ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P]| ≤
      2 * ((((k₁ + k₂) / 2 : ℕ) : ℝ) ^ (k₁ + k₂)) * B / (n + 1 : ℝ) ^ 2 := by
  classical
  have := hindep.isProbabilityMeasure
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans
      (hη 0 (Nat.zero_lt_succ n))
  have h0B : ∫ _ω : Ω, (0 : ℝ) ^ (k₁ + k₂) ∂P ≤ B := by
    rcases eq_or_ne (k₁ + k₂) 0 with hk | hk
    · simpa [hk] using hη 0 (Nat.zero_lt_succ n)
    · simpa [zero_pow hk] using hB
  have ⟨hξzero', hξp', hξ'⟩ := ite_zero_memLp_moment (fun ij : StrictUpper ↦ ij.val.2 < n + 1) h0B
    fun ij hij ↦ ⟨hξzero ij hij, hξp ij hij, hξ ij hij⟩
  have ⟨hηzero', hηp', hη'⟩ := ite_zero_memLp_moment (fun i : ℕ ↦ i < n + 1) h0B
    fun i hi ↦ ⟨hηzero i hi, hηp i hi, hη i hi⟩
  have hcov := abs_covariance_integral_pow_spectralMeasure_wignerMatrix_le_global
    (ξ := fun ij ↦ if ij.val.2 < n + 1 then ξ ij else 0)
    (η := fun i ↦ if i < n + 1 then η i else 0) (k₁ := k₁) (k₂ := k₂) (B := B)
    (iIndepFun_ite_lt hindep) hξzero' hηzero' hξp' hηp' hξ' hη' n
  simp only [wignerMatrix_ite_lt] at hcov
  exact hcov

/-- **Empirical spectral moment variance bound (AGZ Lemma 2.1.7).** Under corner-local
independent centered entries in `L^(2k)` with `2k`-th absolute moments bounded by `B`, the variance
of the `k`-th empirical spectral moment of `Hₙ₊₁` is at most `2 * k^(2k) * B / (n + 1)²` for every
`k` and `n`. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le
    {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n + 1, ∫ ω, η i ω ∂P = 0)
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
    hindep hξzero hηzero (k₁ := k) (k₂ := k)
    (by simpa only [h2k] using hξp) (by simpa only [h2k] using hηp)
    (by simpa only [h2k] using hξ) (by simpa only [h2k] using hη)
  rw [hdiv, h2k] at hcov
  rw [← covariance_self hm]
  exact (le_abs_self _).trans hcov

/-- **Chebyshev tail bound for empirical spectral moments.** Under corner-local independent
centered entries in `L^(2k)` with `2k`-th absolute moments bounded by `B`, the probability that the
`k`-th empirical spectral moment of `Hₙ₊₁` deviates from its expectation by at least `ε > 0` is
bounded by `2 * k^(2k) * B / (n + 1)² / ε²`. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
    {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n + 1, ∫ ω, η i ω ∂P = 0)
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
  have hvar := variance_integral_pow_spectralMeasure_wignerMatrix_le
    hindep hξzero hηzero hξp hηp hξ hη
  exact (meas_ge_le_variance_div_sq hmem hε).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg ε)))

end FixedSpace

section VaryingSpaces

/-- Every expected odd empirical spectral moment of a Wigner matrix converges to zero under
independent centered entries in `L^(2m + 1)` with uniformly bounded `(2m + 1)`-st absolute moments,
including for triangular arrays on varying probability spaces. -/
theorem tendsto_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {m : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * m + 1 : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * m + 1 : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * m + 1) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * m + 1) ∂P n ≤ B) :
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
        (iIndepFun_sumElim_ofReal_subtype_lt (hindep n)) (fun ij _ ↦ hξzero n ij)
        (fun i _ ↦ hηzero n i) (fun ij _ ↦ hξp n ij) (fun i _ ↦ hηp n i)
        (fun ij _ ↦ hξ n ij) (fun i _ ↦ hη n i)) hlim

/-- Empirical spectral moment fluctuations around their expectations vanish in probability under
corner-local independent centered entries in `L^(2k)` with uniformly bounded `2k`-th absolute
moments, including for triangular arrays on varying probability spaces. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P n = 0)
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
  have hlim : Tendsto (fun n : ℕ ↦ 2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hvar : Tendsto (fun n ↦ Var[fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ); P n]) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n ↦ variance_nonneg _ _)
      (fun n ↦ variance_integral_pow_spectralMeasure_wignerMatrix_le
        (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n))
  exact tendsto_measure_abs_sub_integral_ge_of_tendsto_variance hmem hvar hε

private theorem tendsto_measure_abs_sub_ge_of_tendsto_integral
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {X : (n : ℕ) → Ω n → ℝ} {c : ℝ}
    (hmean : Tendsto (fun n ↦ ∫ ω, X n ω ∂P n) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε)
    (hfluc : Tendsto (fun n ↦ P n {ω | ε / 2 ≤ |X n ω - ∫ ω', X n ω' ∂P n|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ P n {ω | ε ≤ |X n ω - c|}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
    (.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [Metric.tendsto_nhds.1 hmean (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq] at hn
  refine measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith [abs_sub_le (X n ω) (∫ ω', X n ω' ∂P n) c]

/-- Every odd empirical spectral moment of a Wigner matrix converges to zero in probability under
independent centered entries in `L^(4m + 2)` with uniformly bounded `(4m + 2)`-th absolute moments,
including for triangular arrays on varying probability spaces. -/
theorem tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
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
  have (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hξ' (n ij) := (hξp n ij).memLp_and_integral_norm_pow_le_sqrt (hξ n ij)
  have hη' (n i) := (hηp n i).memLp_and_integral_norm_pow_le_sqrt (hη n i)
  have hmean := tendsto_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
    hindep hξzero hηzero (fun n ij ↦ (hξ' n ij).1) (fun n i ↦ (hη' n i).1)
    (fun n ij ↦ (hξ' n ij).2) (fun n i ↦ (hη' n i).2)
  have hfluc := tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    (fun n ↦ iIndepFun_sumElim_ofReal_subtype_lt (hindep n))
    (fun n ij _ ↦ hξzero n ij) (fun n i _ ↦ hηzero n i)
    (fun n ij _ ↦ hξp n ij) (fun n i _ ↦ hηp n i)
    (fun n ij _ ↦ hξ n ij) (fun n i _ ↦ hη n i) (half_pos hε)
  simpa only [sub_zero] using tendsto_measure_abs_sub_ge_of_tendsto_integral hmean hε hfluc

/-- **Convergence in probability of empirical spectral moments.** On possibly varying probability
spaces, when all entries in each corner are centered, the diagonal and strictly upper-triangular
entries are jointly independent within each corner, both entry families lie in `L^(2k)` in each
corner with uniformly bounded `2k`-th absolute moment integrals, and the strictly upper-triangular
entries have common second absolute moment `s`, the `k`-th empirical spectral moment converges in
probability to the `k`-th moment of `semicircleReal 0 s`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P n = 0)
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, x ^ k ∂semicircleReal 0 s|}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hξ' (n ij hij) := (hξp n ij hij).memLp_and_integral_norm_pow_le_sqrt (hξ n ij hij)
  have hη' (n i hi) := (hηp n i hi).memLp_and_integral_norm_pow_le_sqrt (hη n i hi)
  have hmean := tendsto_integral_integral_pow_spectralMeasure_wignerMatrix' (k := k) (B := √B)
    (s := s) hindep hξzero hηzero (fun n ij hij ↦ (hξ' n ij hij).1)
    (fun n i hi ↦ (hη' n i hi).1) (fun n ij hij ↦ (hξ' n ij hij).2)
    (fun n i hi ↦ (hη' n i hi).2) hξsq
  have hfluc := tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    hindep hξzero hηzero hξp hηp hξ hη (half_pos hε)
  exact tendsto_measure_abs_sub_ge_of_tendsto_integral hmean hε hfluc

end VaryingSpaces

end TauCeti.Probability
