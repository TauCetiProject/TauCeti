/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.RandomMatrix.MomentBounds
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Analysis.RCLike.Sum
import TauCeti.Combinatorics.TreeWalk.ConnectedPair
import TauCeti.Probability.Moments.Chebyshev

/-!
# Expected spectral moments and variance bounds for Wigner matrices

This file completes the moment-method estimates for Hermitian Wigner matrices of all moment
orders `k : ℕ`:

1. **Expected moments.** Combining the Catalan-times-descending-factorial count of leading cyclic
   trace words (`card_filter_leadingCyclicWord`) with the `n⁻ᵐ` expectation of each leading word
   and the `O(n⁻¹)` / `O(n⁻¹/²)` bounds on nonleading and odd words (`MomentBounds`), the expected
   `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)` converges to the `k`th moment of
   the standard semicircle law `semicircleReal 0 1` (`catalan m` for `k = 2 * m` and `0` for odd
   `k`).
2. **`O_k(n⁻²)` variance bounds and concentration.** Expanding the variance of the `k`th empirical
   spectral moment over pairs of cyclic trace words `(w₁, w₂)`, pairs with disjoint unordered edge
   sets cancel by independence and pairs whose combined step family contains a singleton unordered
   edge vanish by centering. The remaining pairs share an unordered edge and have no combined
   singleton unordered edge, so there are at most `(n + 1) ^ k * k ^ (2 * k)` of them
   (`card_filter_connectedPair_le`), each bounded in magnitude by `2 * (n + 1)⁻¹ ^ k * B`. This
   gives `Var[∫ x ^ k dL_{H_{n+1}}] ≤ 2 * k ^ (2 * k) * B / (n + 1) ^ 2`, Chebyshev tail bounds,
   convergence in probability on varying sample spaces, and Borel–Cantelli almost-sure convergence
   without any coupling assumption across matrix sizes `n`.

## Main results

In the `TauCeti.Probability` namespace:

* `abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le` and
  `abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le`: quantitative
  `O(n⁻¹)` and `O(n⁻¹/²)` error bounds on expected even and odd empirical spectral moments of
  `wignerMatrix ξ η (n + 1)`.
* `tendsto_integral_integral_pow_spectralMeasure_wignerMatrix`: convergence of expected `k`th
  empirical spectral moments to the `k`th moments of `semicircleReal 0 1`.
* `memLp_integral_pow_spectralMeasure_wignerMatrix`: `Lᵖ` membership of the `k`th empirical
  spectral moment from `L^{p * k}` corner entries.
* `variance_integral_pow_spectralMeasure_wignerMatrix_le`: quantitative
  `2 * k ^ (2 * k) * B / (n + 1) ^ 2` bound on the variance of the `k`th empirical spectral moment.
* `tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability`: convergence
  in probability of the `k`th empirical spectral moment on possibly varying sample spaces.
* `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq` and
  `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix`: almost-sure convergence of the `k`th
  empirical spectral moment via Borel–Cantelli.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemmas 2.1.6 and 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology ENNReal

namespace TauCeti.Probability

section ExpectedMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Quantitative `O(n⁻¹)` error bound between the expected `2 * m`th empirical spectral moment of
`wignerMatrix ξ η (n + 1)` and the `2 * m`th moment of `semicircleReal 0 1`, requiring hypotheses
only on the `(n + 1) × (n + 1)` corner. -/
theorem abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le
    {m n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) P)
    (hξzero : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n + 1 → ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    |(∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) -
      ∫ x, x ^ (2 * m) ∂semicircleReal 0 1| ≤
      ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / (n + 1 : ℝ) := by
  have heq : ((∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P : ℝ) : ℂ) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ (2 * m)).trace ∂P := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    simpa only [RCLike.ofReal_eq_complex_ofReal, Fintype.card_fin] using
      Matrix.ofReal_integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
        (wignerMatrix_isHermitian ξ η ω (n + 1)) (2 * m)
  have h := norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le (n := n + 1)
    (Nat.succ_ne_zero n) hindep hξzero hηzero hsecond hξp hηp hξ hη
  rw [← heq] at h
  rw [integral_pow_two_mul_semicircleReal_zero, NNReal.coe_one, one_pow, one_mul]
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using h

/-- Quantitative `O(n⁻¹/²)` bound on the expected `(2 * m + 1)`st empirical spectral moment of
`wignerMatrix ξ η (n + 1)`, requiring hypotheses only on the `(n + 1) × (n + 1)` corner. -/
theorem abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
    {m n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) P)
    (hξzero : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n + 1 → ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℝ) := by
  have heq : ((∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P : ℝ) : ℂ) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ (2 * m + 1)).trace ∂P := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    simpa only [RCLike.ofReal_eq_complex_ofReal, Fintype.card_fin] using
      Matrix.ofReal_integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
        (wignerMatrix_isHermitian ξ η ω (n + 1)) (2 * m + 1)
  have h := norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le_of_lt (n := n + 1)
    hindep hξzero hηzero hξp hηp hξ hη
  rw [← heq] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using h

/-- For Wigner matrices on (possibly varying) probability spaces whose `(n + 1) × (n + 1)` corner
entries are independent and centered with unit off-diagonal second moments and uniformly bounded
`k`th absolute moments, the expected `k`th empirical spectral moment converges to the `k`th moment
of `semicircleReal 0 1`. -/
theorem tendsto_integral_integral_pow_spectralMeasure_wignerMatrix
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) (P n))
    (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (k : ℝ≥0∞) (P n))
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (k : ℝ≥0∞) (P n))
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / (n + 1 : ℝ))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hlim
    simpa only [Real.norm_eq_abs] using
      abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le
        (hindep n) (hξzero n) (hηzero n) (hsecond n)
        (fun ij hij ↦ by simpa using hξp n ij hij)
        (fun i hi ↦ by simpa using hηp n i hi) (hξ n) (hη n)
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hlim
    simpa only [sub_zero, Real.norm_eq_abs] using
      abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
        (hindep n) (hξzero n) (hηzero n)
        (fun ij hij ↦ by simpa using hξp n ij hij)
        (fun i hi ↦ by simpa using hηp n i hi) (hξ n) (hη n)

end ExpectedMoments

section VarianceAndConcentration

/-- The `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)` lies in `Lᵖ` whenever the
entries of the `(n + 1) × (n + 1)` corner lie in `L^{p * k}`. -/
theorem memLp_integral_pow_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {p : ℝ≥0∞} {k n : ℕ}
    (hξ : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (p * k) P)
    (hη : ∀ i, i < n + 1 → MemLp (η i) (p * k) P) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) p P := by
  have hZ : MemLp (fun ω ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace) p P := by
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using (memLp_const ((n + 1 : ℕ) : ℂ)).const_mul _
    · simp_rw [trace_pow_eq_sum_prod _ hk]
      have hξ' : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (p * Fintype.card (Fin k)) P := by
        rwa [Fintype.card_fin]
      have hη' : ∀ i, i < n + 1 → MemLp (η i) (p * Fintype.card (Fin k)) P := by
        rwa [Fintype.card_fin]
      exact (memLp_finsetSum (univ : Finset (Fin k → Fin (n + 1))) fun w _ ↦
        memLp_prod_wignerMatrix_apply hξ' hη' w (w ∘ finRotate k)).const_mul _
  have hre (ω : Ω) :
      Complex.reCLM (((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace) =
        ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) := by
    have h := Matrix.ofReal_integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
      (wignerMatrix_isHermitian ξ η ω (n + 1)) k
    simp only [RCLike.ofReal_eq_complex_ofReal, Fintype.card_fin] at h
    rw [← h, Complex.reCLM_apply, Complex.ofReal_re]
  simpa only [Function.comp_def, hre] using Complex.reCLM.comp_memLp' hZ

private theorem prod_mul_star_prod_wignerMatrix_apply_eq {Ω : Type*}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} (ω : Ω)
    (w₁ w₂ : Fin k → Fin n) :
    (∏ s, wignerMatrix ξ η n ω (w₁ s) (w₁ (finRotate k s))) *
        star (∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t))) =
      ∏ x : Fin k ⊕ Fin k, wignerMatrix ξ η n ω
        (Sum.elim w₁ (w₂ ∘ finRotate k) x)
        (Sum.elim (w₁ ∘ finRotate k) w₂ x) := by
  rw [star_prod_wignerMatrix_apply, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]

private theorem norm_integral_prod_mul_star_prod_wignerMatrix_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} (hk : k ≠ 0) {B : ℝ}
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w₁ w₂ : Fin k → Fin (n + 1)) :
    ‖∫ ω, (∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s))) *
        star (∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t))) ∂P‖ ≤
      (n + 1 : ℝ)⁻¹ ^ k * B := by
  have : Nonempty (Fin k ⊕ Fin k) := ⟨.inl ⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  simp_rw [prod_mul_star_prod_wignerMatrix_apply_eq]
  have h := norm_integral_prod_wignerMatrix_apply_le_of_lt (ι := Fin k ⊕ Fin k)
    (fun ij hij ↦ by simpa [hcard] using hξp ij hij)
    (fun i hi ↦ by simpa [hcard] using hηp i hi)
    (fun ij hij ↦ by simpa [hcard] using hξ ij hij)
    (fun i hi ↦ by simpa [hcard] using hη i hi)
    (Sum.elim w₁ (w₂ ∘ finRotate k)) (Sum.elim (w₁ ∘ finRotate k) w₂)
  have hs : (Real.sqrt (n + 1 : ℕ))⁻¹ ^ (2 * k) = (n + 1 : ℝ)⁻¹ ^ k := by
    rw [inv_pow, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _), inv_pow, Nat.cast_add, Nat.cast_one]
  rwa [hcard, hs] at h

private theorem norm_integral_prod_wignerMatrix_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} (hk : k ≠ 0) {B : ℝ}
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w : Fin k → Fin (n + 1)) :
    ‖∫ ω, ∏ s, wignerMatrix ξ η (n + 1) ω (w s) (w (finRotate k s)) ∂P‖ ^ 2 ≤
      (n + 1 : ℝ)⁻¹ ^ k * B := by
  let T : Ω → ℂ := fun ω ↦ ∏ s, wignerMatrix ξ η (n + 1) ω (w s) (w (finRotate k s))
  have hT2 : MemLp (fun ω ↦ ‖T ω‖) 2 P :=
    (memLp_prod_wignerMatrix_apply
      (fun ij hij ↦ by simpa [Fintype.card_fin] using hξp ij hij)
      (fun i hi ↦ by simpa [Fintype.card_fin] using hηp i hi)
      w (w ∘ finRotate k)).norm
  have hcs : (∫ ω, ‖T ω‖ ∂P) ^ 2 ≤ ∫ ω, ‖T ω‖ ^ 2 ∂P := by
    have hvar := variance_nonneg (fun ω ↦ ‖T ω‖) P
    rw [variance_eq_sub hT2] at hvar
    simpa only [Pi.pow_apply] using sub_nonneg.mp hvar
  have hni : ‖∫ ω, T ω ∂P‖ ^ 2 ≤ (∫ ω, ‖T ω‖ ∂P) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm T) 2
  have hsq : ∫ ω, ‖T ω‖ ^ 2 ∂P = ‖∫ ω, T ω * star (T ω) ∂P‖ := by
    have hnn : 0 ≤ ∫ ω, ‖T ω‖ ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
    have hmul (ω : Ω) : T ω * star (T ω) = ((‖T ω‖ ^ 2 : ℝ) : ℂ) := by
      simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (T ω)
    simp_rw [hmul, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnn]
  exact (hni.trans hcs).trans (hsq ▸
    norm_integral_prod_mul_star_prod_wignerMatrix_le hk hξp hηp hξ hη w w)

private theorem ofReal_variance_eq_mul_sum_cov {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Fintype ι] {X : Ω → ℝ} (hX2 : MemLp X 2 P)
    {c : ℂ} (hc : star c = c) {T : ι → Ω → ℂ}
    (hX : ∀ ω, ((X ω : ℝ) : ℂ) = c * ∑ i, T i ω)
    (hT : ∀ i, Integrable (T i) P)
    (hTT : ∀ i j, Integrable (fun ω ↦ T i ω * star (T j ω)) P) :
    ((Var[X; P] : ℝ) : ℂ) = c ^ 2 * ∑ p : ι × ι,
      ((∫ ω, T p.1 ω * star (T p.2 ω) ∂P) -
        (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P)) := by
  have hmean : ((∫ ω, X ω ∂P : ℝ) : ℂ) = c * ∑ i, ∫ ω, T i ω ∂P := by
    rw [← integral_complex_ofReal]
    simp_rw [hX]
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hT i]
  have hsq_pt (ω : Ω) : ((X ω ^ 2 : ℝ) : ℂ) =
      c ^ 2 * ∑ p : ι × ι, T p.1 ω * star (T p.2 ω) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      RCLike.ofReal_sq_eq_mul_sum_mul_star (𝕜 := ℂ) hc (by simpa using hX ω)
  have hsq : ((∫ ω, X ω ^ 2 ∂P : ℝ) : ℂ) =
      c ^ 2 * ∑ p : ι × ι, ∫ ω, T p.1 ω * star (T p.2 ω) ∂P := by
    rw [← integral_complex_ofReal]
    simp_rw [hsq_pt]
    rw [integral_const_mul, integral_finsetSum _ fun p _ ↦ hTT p.1 p.2]
  have hmean_sq : (((∫ ω, X ω ∂P) ^ 2 : ℝ) : ℂ) =
      c ^ 2 * ∑ p : ι × ι, (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      RCLike.ofReal_sq_eq_mul_sum_mul_star (𝕜 := ℂ) hc (by simpa using hmean)
  rw [variance_eq_sub hX2]
  simp only [Pi.pow_apply, Complex.ofReal_sub]
  rw [hsq, hmean_sq, ← mul_sub, ← Finset.sum_sub_distrib]

private theorem integral_prod_mul_star_prod_sub_eq_zero_of_not_isConnectedPair
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ}
    (hξm : ∀ ij, ij.1.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i, i < n → AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n r)) P)
    (hξzero : ∀ ij, ij.1.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n → ∫ ω, η i ω ∂P = 0)
    {w₁ w₂ : Fin k → Fin n} (hnot : ¬ TreeWalk.IsConnectedPair w₁ w₂) :
    (∫ ω, (∏ s, wignerMatrix ξ η n ω (w₁ s) (w₁ (finRotate k s))) *
        star (∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t))) ∂P) -
      (∫ ω, ∏ s, wignerMatrix ξ η n ω (w₁ s) (w₁ (finRotate k s)) ∂P) *
        star (∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t)) ∂P) = 0 := by
  by_cases hshare : ∃ t₁ t₂,
      s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂))
  · -- Combined singleton edge: both the joint expectation and one factor vanish by centering.
    obtain ⟨x₀, hx₀⟩ := not_forall.mp (not_and.mp hnot hshare)
    have hedges (y : Fin k ⊕ Fin k) :
        s(Sum.elim w₁ (w₂ ∘ finRotate k) y, Sum.elim (w₁ ∘ finRotate k) w₂ y) =
          Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
            (fun t ↦ s(w₂ t, w₂ (finRotate k t))) y := by
      cases y <;> simp [Sym2.eq_swap]
    have hzero1 : ∫ ω, (∏ s, wignerMatrix ξ η n ω (w₁ s) (w₁ (finRotate k s))) *
        star (∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t))) ∂P = 0 := by
      simp_rw [prod_mul_star_prod_wignerMatrix_apply_eq]
      exact integral_prod_wignerMatrix_apply_eq_zero_of_lt hξm hηm hindep hξzero hηzero
        (Sum.elim w₁ (w₂ ∘ finRotate k)) (Sum.elim (w₁ ∘ finRotate k) w₂)
        (t := x₀) fun y hy ↦ by_contra fun hne ↦
          hx₀ ⟨y, hne, by rwa [← hedges y, ← hedges x₀]⟩
    have hzero2 : (∫ ω, ∏ s, wignerMatrix ξ η n ω (w₁ s) (w₁ (finRotate k s)) ∂P) *
        star (∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t)) ∂P) = 0 := by
      cases x₀ with
      | inl s₀ =>
        have hz : ∫ ω, ∏ s, wignerMatrix ξ η n ω (w₁ s) (w₁ (finRotate k s)) ∂P = 0 :=
          integral_prod_wignerMatrix_apply_eq_zero_of_lt hξm hηm hindep hξzero hηzero
            w₁ (w₁ ∘ finRotate k) (t := s₀) fun s hs ↦ by_contra fun hne ↦
              hx₀ ⟨.inl s, Sum.inl_injective.ne hne, by simpa using hs⟩
        rw [hz, zero_mul]
      | inr t₀ =>
        have hz : ∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t)) ∂P = 0 :=
          integral_prod_wignerMatrix_apply_eq_zero_of_lt hξm hηm hindep hξzero hηzero
            w₂ (w₂ ∘ finRotate k) (t := t₀) fun t ht ↦ by_contra fun hne ↦
              hx₀ ⟨.inr t, Sum.inr_injective.ne hne, by simpa using ht⟩
        rw [hz, star_zero, mul_zero]
    rw [hzero1, hzero2, sub_zero]
  · -- Disjoint unordered edge sets: the expectation of the product factors by independence.
    have hdisj (s t : Fin k) :
        s(w₁ s, w₁ (finRotate k s)) ≠ s(w₂ (finRotate k t), w₂ t) := by
      rw [Sym2.eq_swap (a := w₂ (finRotate k t))]
      exact fun h ↦ hshare ⟨s, t, h⟩
    have hmul := integral_prod_mul_prod_wignerMatrix_apply_eq_mul_integral
      hξm hηm hindep w₁ (w₁ ∘ finRotate k) (w₂ ∘ finRotate k) w₂ hdisj
    simp only [Function.comp_apply] at hmul
    have hconj : star (∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t)) ∂P) =
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ (finRotate k t)) (w₂ t) ∂P :=
      calc
        star (∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t)) ∂P)
          = ∫ ω, star (∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t))) ∂P :=
            integral_conj.symm
        _ = ∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ (finRotate k t)) (w₂ t) ∂P :=
            integral_congr_ae (.of_forall fun ω ↦
              star_prod_wignerMatrix_apply ξ η ω w₂ (w₂ ∘ finRotate k))
    rw [sub_eq_zero, hconj, ← hmul]
    exact integral_congr_ae (.of_forall fun ω ↦
      congrArg (_ * ·) (star_prod_wignerMatrix_apply ξ η ω w₂ fun t ↦ w₂ (finRotate k t)))

private theorem norm_integral_prod_mul_star_prod_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} (hk : k ≠ 0) {B : ℝ}
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w₁ w₂ : Fin k → Fin (n + 1)) :
    ‖(∫ ω, (∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s))) *
        star (∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t))) ∂P) -
      (∫ ω, ∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s)) ∂P) *
        star (∫ ω, ∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t)) ∂P)‖ ≤
      2 * (n + 1 : ℝ)⁻¹ ^ k * B := by
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0 (Nat.zero_lt_succ n))
  have h1 := norm_integral_prod_mul_star_prod_wignerMatrix_le hk hξp hηp hξ hη w₁ w₂
  have h2₁ := norm_integral_prod_wignerMatrix_sq_le hk hξp hηp hξ hη w₁
  have h2₂ := norm_integral_prod_wignerMatrix_sq_le hk hξp hηp hξ hη w₂
  have hprod : ‖(∫ ω, ∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s)) ∂P) *
      star (∫ ω, ∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t)) ∂P)‖ ≤
      (n + 1 : ℝ)⁻¹ ^ k * B := by
    rw [norm_mul, norm_star]
    have hsq_mul :
        (‖∫ ω, ∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s)) ∂P‖ *
          ‖∫ ω, ∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t)) ∂P‖) ^ 2 ≤
        ((n + 1 : ℝ)⁻¹ ^ k * B) ^ 2 := by
      rw [mul_pow, sq ((n + 1 : ℝ)⁻¹ ^ k * B)]
      exact mul_le_mul h2₁ h2₂ (sq_nonneg _) (mul_nonneg (by positivity) hB)
    exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (by positivity) hB)
      (by simpa only [sq] using hsq_mul)
  calc
    _ ≤ ‖∫ ω, (∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s))) *
          star (∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t))) ∂P‖ +
        ‖(∫ ω, ∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s)) ∂P) *
          star (∫ ω, ∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t)) ∂P)‖ :=
      norm_sub_le _ _
    _ ≤ (n + 1 : ℝ)⁻¹ ^ k * B + (n + 1 : ℝ)⁻¹ ^ k * B := add_le_add h1 hprod
    _ = 2 * (n + 1 : ℝ)⁻¹ ^ k * B := by ring

/-- **Variance bound for Wigner empirical spectral moments** (Anderson–Guionnet–Zeitouni,
Lemma 2.1.7). For independent centered entries on the `(n + 1) × (n + 1)` corner with `2 * k`th
absolute moments bounded by `B`, the variance of the `k`th empirical spectral moment of
`wignerMatrix ξ η (n + 1)` is at most `2 * k ^ (2 * k) * B / (n + 1) ^ 2`. No identical
distribution or second-moment normalization is required. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) P)
    (hξzero : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n + 1 → ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0 (Nat.zero_lt_succ n))
  rcases eq_or_ne k 0 with rfl | hk
  · have hconst : (fun ω ↦ ∫ x, x ^ 0 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) = fun _ ↦ 1 := by
      ext ω
      simp
    rw [hconst, variance_eq_sub (memLp_const 1)]
    simp only [Pi.pow_apply, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one,
      sub_self]
    positivity
  · -- Expand `Var[X; P]` into trace-word covariances, restrict to `IsConnectedPair`, and count.
    let X : Ω → ℝ := fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)
    let T (w : Fin k → Fin (n + 1)) (ω : Ω) : ℂ :=
      ∏ s, wignerMatrix ξ η (n + 1) ω (w s) (w (finRotate k s))
    let covTerm (p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1))) : ℂ :=
      (∫ ω, T p.1 ω * star (T p.2 ω) ∂P) -
        (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P)
    let G : Finset ((Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1))) :=
      {p | TreeWalk.IsConnectedPair p.1 p.2}
    have hX2 : MemLp X 2 P := memLp_integral_pow_spectralMeasure_wignerMatrix
      (fun ij hij ↦ by simpa [Nat.cast_mul] using hξp ij hij)
      (fun i hi ↦ by simpa [Nat.cast_mul] using hηp i hi)
    have hξpk {ij : StrictUpper} (hij : ij.1.2 < n + 1) : MemLp (ξ ij) (k : ℕ) P :=
      (hξp ij hij).mono_exponent (by norm_cast; omega)
    have hηpk {i : ℕ} (hi : i < n + 1) : MemLp (η i) (k : ℕ) P :=
      (hηp i hi).mono_exponent (by norm_cast; omega)
    have hintT (w : Fin k → Fin (n + 1)) : Integrable (T w) P :=
      memLp_one_iff_integrable.mp (memLp_prod_wignerMatrix_apply
        (fun ij hij ↦ by simpa [Fintype.card_fin] using hξpk hij)
        (fun i hi ↦ by simpa [Fintype.card_fin] using hηpk hi) w (w ∘ finRotate k))
    have hintTT (w₁ w₂ : Fin k → Fin (n + 1)) :
        Integrable (fun ω ↦ T w₁ ω * star (T w₂ ω)) P := by
      have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
        rw [Fintype.card_sum, Fintype.card_fin, two_mul]
      simp_rw [T, prod_mul_star_prod_wignerMatrix_apply_eq]
      exact memLp_one_iff_integrable.mp (memLp_prod_wignerMatrix_apply
        (fun ij hij ↦ by simpa [hcard] using hξp ij hij)
        (fun i hi ↦ by simpa [hcard] using hηp i hi) _ _)
    have hXeq (ω : Ω) : ((X ω : ℝ) : ℂ) =
        ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ w : Fin k → Fin (n + 1), T w ω := by
      have h := Matrix.ofReal_integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
        (wignerMatrix_isHermitian ξ η ω (n + 1)) k
      simp only [RCLike.ofReal_eq_complex_ofReal, Fintype.card_fin] at h
      rw [h, trace_pow_eq_sum_prod _ hk]
    have hvarC := ofReal_variance_eq_mul_sum_cov hX2 (by simp) hXeq hintT hintTT
    have hsumG : (∑ p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1)), covTerm p) =
        ∑ p ∈ G, covTerm p :=
      (Finset.sum_subset (Finset.subset_univ G) fun p _ hpG ↦
        integral_prod_mul_star_prod_sub_eq_zero_of_not_isConnectedPair
          (fun ij hij ↦ (hξpk hij).aemeasurable) (fun i hi ↦ (hηpk hi).aemeasurable)
          hindep hξzero hηzero (by simpa [G] using hpG)).symm
    have hGcard : (#G : ℝ) ≤ (n + 1 : ℝ) ^ k * (k : ℝ) ^ (2 * k) := by
      have hc := TreeWalk.card_filter_connectedPair_le (α := Fin (n + 1)) k
      simp only [Fintype.card_fin] at hc
      exact_mod_cast hc
    have hvar_norm : Var[X; P] = ‖((Var[X; P] : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (variance_nonneg X P)]
    have hcancel : (n + 1 : ℝ) ^ k * (n + 1 : ℝ)⁻¹ ^ k = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    rw [hvar_norm, hvarC, hsumG, norm_mul, norm_pow, norm_inv, Complex.norm_natCast,
      Nat.cast_add, Nat.cast_one]
    calc
      (n + 1 : ℝ)⁻¹ ^ 2 * ‖∑ p ∈ G, covTerm p‖
        ≤ (n + 1 : ℝ)⁻¹ ^ 2 * ∑ p ∈ G, ‖covTerm p‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le G covTerm) (by positivity)
      _ ≤ (n + 1 : ℝ)⁻¹ ^ 2 * ∑ _p ∈ G, (2 * (n + 1 : ℝ)⁻¹ ^ k * B) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun p _ ↦
              norm_integral_prod_mul_star_prod_sub_le hk hξp hηp hξ hη p.1 p.2)
            (by positivity)
      _ = (n + 1 : ℝ)⁻¹ ^ 2 * ((#G : ℝ) * (2 * (n + 1 : ℝ)⁻¹ ^ k * B)) := by simp
      _ ≤ (n + 1 : ℝ)⁻¹ ^ 2 *
            (((n + 1 : ℝ) ^ k * (k : ℝ) ^ (2 * k)) * (2 * (n + 1 : ℝ)⁻¹ ^ k * B)) := by gcongr
      _ = ((n + 1 : ℝ) ^ k * (n + 1 : ℝ)⁻¹ ^ k) *
            (2 * (k : ℝ) ^ (2 * k) * B * (n + 1 : ℝ)⁻¹ ^ 2) := by ring
      _ = 2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
          rw [hcancel, one_mul, div_eq_mul_inv, inv_pow]

/-- Chebyshev's tail bound for the `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)`
around its expectation, requiring hypotheses only on the `(n + 1) × (n + 1)` corner. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) P)
    (hξzero : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n + 1 → ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hmem : MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P :=
    memLp_integral_pow_spectralMeasure_wignerMatrix
      (fun ij hij ↦ by simpa [Nat.cast_mul] using hξp ij hij)
      (fun i hi ↦ by simpa [Nat.cast_mul] using hηp i hi)
  refine (meas_ge_le_variance_div_sq hmem hε).trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right
    (variance_integral_pow_spectralMeasure_wignerMatrix_le
      hindep hξzero hηzero hξp hηp hξ hη)
    (sq_nonneg ε)

/-- Fluctuations of the `k`th empirical spectral moment around its expectation vanish in
probability, including on varying probability spaces. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) (P n))
    (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n|})
      atTop (𝓝 0) :=
  TauCeti.tendsto_measure_abs_ge_of_le_div_add_one_sq fun n ↦
    measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) hε

/-- For Wigner matrices on (possibly varying) probability spaces whose `(n + 1) × (n + 1)` corner
entries are independent and centered with unit off-diagonal second moments and uniformly bounded
`2 * k`th absolute moments, the `k`th empirical spectral moment converges in probability to the
`k`th moment of `semicircleReal 0 1`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) (P n))
    (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, x ^ k ∂semicircleReal 0 1|}) atTop (𝓝 0) := by
  have hprob (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hmean := tendsto_integral_integral_pow_spectralMeasure_wignerMatrix (k := k)
    hindep hξzero hηzero hsecond
    (fun n ij hij ↦ (hξp n ij hij).mono_exponent (by norm_cast; omega))
    (fun n i hi ↦ (hηp n i hi).mono_exponent (by norm_cast; omega))
    (fun n ij hij ↦ MeasureTheory.integral_norm_pow_le_one_add_of_le (by omega)
      (hξp n ij hij) (hξ n ij hij))
    (fun n i hi ↦ MeasureTheory.integral_norm_pow_le_one_add_of_le (by omega)
      (hηp n i hi) (hη n i hi))
  have hfluc := tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    hindep hξzero hηzero hξp hηp hξ hη (half_pos hε)
  have hev : ∀ᶠ n in atTop,
      P n {ω | ε ≤
        |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
        ∫ x, x ^ k ∂semicircleReal 0 1|} ≤
      P n {ω | ε / 2 ≤
        |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
        ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n|} := by
    filter_upwards [Metric.tendsto_nhds.1 hmean (ε / 2) (half_pos hε)] with n hn
    rw [Real.dist_eq] at hn
    refine measure_mono fun ω hω ↦ ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith [abs_sub_le
      (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      (∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n)
      (∫ x, x ^ k ∂semicircleReal 0 1)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
    (Eventually.of_forall fun _ ↦ bot_le) hev

/-- Fluctuations of the `k`th empirical spectral moment around its expectation tend almost surely to
zero for any sequence of Wigner arrays on `(Ω, P)` whose `(n + 1) × (n + 1)` corner entries are
independent and centered at each matrix size with uniformly bounded `2 * k`th absolute moments. No
independence across different matrix sizes is required. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) P)
    (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P = 0)
    (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P = 0)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) :=
  TauCeti.ae_tendsto_zero_of_measure_abs_ge_le_div_add_one_sq fun hε n ↦
    measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) hε

/-- Almost-sure convergence of the `k`th empirical spectral moment to the `k`th moment of
`semicircleReal 0 1` for any sequence of Wigner arrays `(ξ n, η n)` on `(Ω, P)` whose
`(n + 1) × (n + 1)` corner entries at each size are independent and centered with unit off-diagonal
second moments and uniformly bounded `2 * k`th absolute moments. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) P)
    (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P = 0)
    (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P = 0)
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have : IsProbabilityMeasure P := (hindep 0).isProbabilityMeasure
  have hmean := tendsto_integral_integral_pow_spectralMeasure_wignerMatrix
    (P := fun _ ↦ P) (k := k) hindep hξzero hηzero hsecond
    (fun n ij hij ↦ (hξp n ij hij).mono_exponent (by norm_cast; omega))
    (fun n i hi ↦ (hηp n i hi).mono_exponent (by norm_cast; omega))
    (fun n ij hij ↦ MeasureTheory.integral_norm_pow_le_one_add_of_le (by omega)
      (hξp n ij hij) (hξ n ij hij))
    (fun n i hi ↦ MeasureTheory.integral_norm_pow_le_one_add_of_le (by omega)
      (hηp n i hi) (hη n i hi))
  filter_upwards [ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    hindep hξzero hηzero hξp hηp hξ hη] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hmean

/-- Almost-sure convergence of the `k`th empirical spectral moment to the `k`th moment of
`semicircleReal 0 1` for the corners of a single infinite Wigner array `(ξ, η)` with independent
centered entries, unit off-diagonal second moments, and uniformly bounded `2 * k`th absolute
moments. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) :=
  ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
    (fun n ↦ hindep.precomp (wignerCoordinateIndex_injective (n + 1)))
    (fun _ ij _ ↦ hξzero ij) (fun _ i _ ↦ hηzero i) (fun _ ij _ ↦ hsecond ij)
    (fun _ ij _ ↦ hξp ij) (fun _ i _ ↦ hηp i) (fun _ ij _ ↦ hξ ij) (fun _ i _ ↦ hη i)

end VarianceAndConcentration

end TauCeti.Probability
