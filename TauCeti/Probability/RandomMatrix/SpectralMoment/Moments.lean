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

Moment-method estimates for `(n + 1) × (n + 1)` Hermitian Wigner matrices of all orders `k : ℕ`:
expected empirical spectral moments converge to `semicircleReal 0 1` at rate `O(n⁻¹)` (even) or
`O(n⁻¹/²)` (odd), and their variance is `O(n⁻²)` via the connected-pair count
`card_filter_connectedPair_le`, yielding convergence in probability (on varying probability spaces)
and almost surely via Borel–Cantelli.

## Main results

* `abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le`,
  `abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le`,
  `tendsto_integral_integral_pow_spectralMeasure_wignerMatrix`: expected moment bounds and limits.
* `memLp_integral_pow_spectralMeasure_wignerMatrix`,
  `variance_integral_pow_spectralMeasure_wignerMatrix_le`,
  `measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge`: `Lᵖ` membership, `O(n⁻²)`
  variance bound, and Chebyshev tail bound.
* `tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability`,
  `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq`,
  `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix`: convergence in probability and a.s.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemmas 2.1.6 and 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology ENNReal

namespace TauCeti.Probability

section ExpectedMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

private theorem ofReal_integral_integral_pow_spectralMeasure_wignerMatrix (k n : ℕ) :
    ((∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P : ℝ) : ℂ) =
      ((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ k).trace ∂P := by
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simpa only [RCLike.ofReal_eq_complex_ofReal, Fintype.card_fin] using
    Matrix.ofReal_integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
      (wignerMatrix_isHermitian ξ η ω (n + 1)) k

section Corner

variable {m n : ℕ} {B : ℝ}
  (hindep : iIndepFun
    (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) P)
  (hξzero : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
  (hηzero : ∀ i, i < n + 1 → ∫ ω, η i ω ∂P = 0)
include hindep hξzero hηzero

/-- Quantitative `O(n⁻¹)` error bound between the expected `2 * m`th empirical spectral moment of
`wignerMatrix ξ η (n + 1)` and `semicircleReal 0 1`, using only `(n + 1) × (n + 1)` corner
hypotheses. -/
theorem abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le
    (hsecond : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    |(∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) -
      ∫ x, x ^ (2 * m) ∂semicircleReal 0 1| ≤
      ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / (n + 1 : ℝ) := by
  have h := norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le (n := n + 1)
    (Nat.succ_ne_zero n) hindep hξzero hηzero hsecond hξp hηp hξ hη
  rw [← ofReal_integral_integral_pow_spectralMeasure_wignerMatrix] at h
  rw [integral_pow_two_mul_semicircleReal_zero, NNReal.coe_one, one_pow, one_mul]
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using h

/-- Quantitative `O(n⁻¹/²)` bound on the expected `(2 * m + 1)`st empirical spectral moment of
`wignerMatrix ξ η (n + 1)`, using only `(n + 1) × (n + 1)` corner hypotheses. -/
theorem abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
    (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℝ) := by
  have h := norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le_of_lt (n := n + 1)
    hindep hξzero hηzero hξp hηp hξ hη
  rw [← ofReal_integral_integral_pow_spectralMeasure_wignerMatrix] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using h

end Corner

/-- For Wigner matrices on (possibly varying) probability spaces whose `(n + 1) × (n + 1)` corner
entries are independent and centered with unit off-diagonal second moments and uniformly bounded
`k`th absolute moments, the expected `k`th empirical spectral moment converges to the `k`th moment
of `semicircleReal 0 1`. -/
theorem tendsto_integral_integral_pow_spectralMeasure_wignerMatrix
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) (P n))
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
  have hadd : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_const_nhds (x := ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B))
        |>.div_atTop hadd)
    simpa only [Real.norm_eq_abs] using
      abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le
        (hindep n) (hξzero n) (hηzero n) (hsecond n)
        (fun ij hij ↦ by simpa using hξp n ij hij) (fun i hi ↦ by simpa using hηp n i hi)
        (hξ n) (hη n)
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_const_nhds (x := (m + 1 : ℝ) ^ (2 * m + 1) * B)
        |>.div_atTop (Real.tendsto_sqrt_atTop.comp hadd))
    simpa only [sub_zero, Real.norm_eq_abs, Function.comp_apply] using
      abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
        (hindep n) (hξzero n) (hηzero n)
        (fun ij hij ↦ by simpa using hξp n ij hij) (fun i hi ↦ by simpa using hηp n i hi)
        (hξ n) (hη n)

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
      exact (memLp_finsetSum (univ : Finset (Fin k → Fin (n + 1))) fun w _ ↦
        memLp_prod_wignerMatrix_apply (fun ij hij ↦ by simpa [Fintype.card_fin] using hξ ij hij)
          (fun i hi ↦ by simpa [Fintype.card_fin] using hη i hi) w (w ∘ finRotate k)).const_mul _
  have hre (ω : Ω) := Matrix.ofReal_integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
    (wignerMatrix_isHermitian ξ η ω (n + 1)) k
  refine (Complex.reCLM.comp_memLp' hZ).ae_eq (.of_forall fun ω ↦ ?_)
  simpa only [Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Fintype.card_fin,
    Complex.reCLM_apply, Complex.ofReal_re] using congrArg Complex.re (hre ω).symm

section SingleSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

private noncomputable abbrev wignerWord (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) {k n : ℕ}
    (w : Fin k → Fin n) (ω : Ω) : ℂ :=
  ∏ s, wignerMatrix ξ η n ω (w s) (w (finRotate k s))

omit [MeasurableSpace Ω] in
private theorem prod_mul_star_prod_wignerMatrix_apply_eq {k n : ℕ} (ω : Ω)
    (w₁ w₂ : Fin k → Fin n) :
    wignerWord ξ η w₁ ω * star (wignerWord ξ η w₂ ω) =
      ∏ x : Fin k ⊕ Fin k, wignerMatrix ξ η n ω
        (Sum.elim w₁ (w₂ ∘ finRotate k) x) (Sum.elim (w₁ ∘ finRotate k) w₂ x) := by
  rw [wignerWord, wignerWord, star_prod_wignerMatrix_apply, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]

section PrivateBounds

variable {k n : ℕ} (hk : k ≠ 0) {B : ℝ}
  (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
  (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * k : ℕ) P)
  (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
  (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
include hk hξp hηp hξ hη

private theorem norm_integral_prod_mul_star_prod_wignerMatrix_le
    (w₁ w₂ : Fin k → Fin (n + 1)) :
    ‖∫ ω, wignerWord ξ η w₁ ω * star (wignerWord ξ η w₂ ω) ∂P‖ ≤ (n + 1 : ℝ)⁻¹ ^ k * B := by
  have : Nonempty (Fin k ⊕ Fin k) := ⟨.inl ⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by simp [two_mul]
  simp_rw [prod_mul_star_prod_wignerMatrix_apply_eq]
  have h := norm_integral_prod_wignerMatrix_apply_le_of_lt (ι := Fin k ⊕ Fin k)
    (fun ij hij ↦ by simpa [hcard] using hξp ij hij) (fun i hi ↦ by simpa [hcard] using hηp i hi)
    (fun ij hij ↦ by simpa [hcard] using hξ ij hij) (fun i hi ↦ by simpa [hcard] using hη i hi)
    (Sum.elim w₁ (w₂ ∘ finRotate k)) (Sum.elim (w₁ ∘ finRotate k) w₂)
  have hs : (Real.sqrt (n + 1 : ℕ))⁻¹ ^ (2 * k) = (n + 1 : ℝ)⁻¹ ^ k := by
    rw [inv_pow, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _), inv_pow, Nat.cast_add, Nat.cast_one]
  rwa [hcard, hs] at h

private theorem norm_integral_prod_wignerMatrix_sq_le [IsProbabilityMeasure P]
    (w : Fin k → Fin (n + 1)) :
    ‖∫ ω, wignerWord ξ η w ω ∂P‖ ^ 2 ≤ (n + 1 : ℝ)⁻¹ ^ k * B := by
  have hT2 : MemLp (fun ω ↦ ‖wignerWord ξ η w ω‖) 2 P :=
    (memLp_prod_wignerMatrix_apply (fun ij hij ↦ by simpa [Fintype.card_fin] using hξp ij hij)
      (fun i hi ↦ by simpa [Fintype.card_fin] using hηp i hi) w (w ∘ finRotate k)).norm
  have hcs : (∫ ω, ‖wignerWord ξ η w ω‖ ∂P) ^ 2 ≤ ∫ ω, ‖wignerWord ξ η w ω‖ ^ 2 ∂P := by
    simpa only [Pi.pow_apply] using sub_nonneg.mp <|
      (variance_eq_sub hT2).symm ▸ variance_nonneg (fun ω ↦ ‖wignerWord ξ η w ω‖) P
  have hsq : ∫ ω, ‖wignerWord ξ η w ω‖ ^ 2 ∂P =
      ‖∫ ω, wignerWord ξ η w ω * star (wignerWord ξ η w ω) ∂P‖ := by
    simp_rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]
  exact ((pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans hcs).trans
    (hsq ▸ norm_integral_prod_mul_star_prod_wignerMatrix_le hk hξp hηp hξ hη w w)

private theorem norm_integral_prod_mul_star_prod_sub_le [IsProbabilityMeasure P]
    (w₁ w₂ : Fin k → Fin (n + 1)) :
    ‖(∫ ω, wignerWord ξ η w₁ ω * star (wignerWord ξ η w₂ ω) ∂P) -
      (∫ ω, wignerWord ξ η w₁ ω ∂P) * star (∫ ω, wignerWord ξ η w₂ ω ∂P)‖ ≤
      2 * (n + 1 : ℝ)⁻¹ ^ k * B := by
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0 (Nat.zero_lt_succ n))
  have hprod : ‖(∫ ω, wignerWord ξ η w₁ ω ∂P) * star (∫ ω, wignerWord ξ η w₂ ω ∂P)‖ ≤
      (n + 1 : ℝ)⁻¹ ^ k * B := by
    rw [norm_mul, norm_star]
    refine nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (by positivity) hB) ?_
    simpa only [mul_pow, ← sq] using mul_le_mul
      (norm_integral_prod_wignerMatrix_sq_le hk hξp hηp hξ hη w₁)
      (norm_integral_prod_wignerMatrix_sq_le hk hξp hηp hξ hη w₂)
      (sq_nonneg _) (mul_nonneg (by positivity) hB)
  linarith [norm_sub_le (∫ ω, wignerWord ξ η w₁ ω * star (wignerWord ξ η w₂ ω) ∂P)
    ((∫ ω, wignerWord ξ η w₁ ω ∂P) * star (∫ ω, wignerWord ξ η w₂ ω ∂P)),
    norm_integral_prod_mul_star_prod_wignerMatrix_le hk hξp hηp hξ hη w₁ w₂]

end PrivateBounds

private theorem ofReal_variance_eq_mul_sum_cov {ι : Type*} [IsProbabilityMeasure P] [Fintype ι]
    {X : Ω → ℝ} (hX2 : MemLp X 2 P) {c : ℂ} (hc : star c = c) {T : ι → Ω → ℂ}
    (hX : ∀ ω, ((X ω : ℝ) : ℂ) = c * ∑ i, T i ω) (hT : ∀ i, Integrable (T i) P)
    (hTT : ∀ i j, Integrable (fun ω ↦ T i ω * star (T j ω)) P) :
    ((Var[X; P] : ℝ) : ℂ) = c ^ 2 * ∑ p : ι × ι,
      ((∫ ω, T p.1 ω * star (T p.2 ω) ∂P) - (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P)) := by
  have hsqOf {Y : ℝ} {S : ι → ℂ} (hY : ((Y : ℝ) : ℂ) = c * ∑ i, S i) :
      ((Y ^ 2 : ℝ) : ℂ) = c ^ 2 * ∑ p : ι × ι, S p.1 * star (S p.2) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      RCLike.ofReal_sq_eq_mul_sum_mul_star (𝕜 := ℂ) hc (by simpa using hY)
  have hmean : ((∫ ω, X ω ∂P : ℝ) : ℂ) = c * ∑ i, ∫ ω, T i ω ∂P := by
    rw [← integral_complex_ofReal]; simp_rw [hX]
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hT i]
  rw [variance_eq_sub hX2]; simp only [Pi.pow_apply, Complex.ofReal_sub]
  rw [← integral_complex_ofReal, show (fun ω ↦ ((X ω ^ 2 : ℝ) : ℂ)) =
      fun ω ↦ c ^ 2 * ∑ p : ι × ι, T p.1 ω * star (T p.2 ω) from funext fun ω ↦ hsqOf (hX ω),
    integral_const_mul, integral_finsetSum _ fun p _ ↦ hTT p.1 p.2, hsqOf hmean, ← mul_sub,
    ← Finset.sum_sub_distrib]

private theorem integral_prod_mul_star_prod_sub_eq_zero_of_not_isConnectedPair {k n : ℕ}
    (hξm : ∀ ij, ij.1.2 < n → AEMeasurable (ξ ij) P)
    (hηm : ∀ i, i < n → AEMeasurable (η i) P)
    (hindep : iIndepFun
      (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex n r)) P)
    (hξzero : ∀ ij, ij.1.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, i < n → ∫ ω, η i ω ∂P = 0)
    {w₁ w₂ : Fin k → Fin n} (hnot : ¬ TreeWalk.IsConnectedPair w₁ w₂) :
    (∫ ω, wignerWord ξ η w₁ ω * star (wignerWord ξ η w₂ ω) ∂P) -
      (∫ ω, wignerWord ξ η w₁ ω ∂P) * star (∫ ω, wignerWord ξ η w₂ ω ∂P) = 0 := by
  by_cases hshare : ∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂))
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp (not_and.mp hnot hshare)
    have hedges (y : Fin k ⊕ Fin k) :
        s(Sum.elim w₁ (w₂ ∘ finRotate k) y, Sum.elim (w₁ ∘ finRotate k) w₂ y) =
          Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
            (fun t ↦ s(w₂ t, w₂ (finRotate k t))) y := by cases y <;> simp [Sym2.eq_swap]
    have hzero1 : ∫ ω, wignerWord ξ η w₁ ω * star (wignerWord ξ η w₂ ω) ∂P = 0 := by
      simp_rw [prod_mul_star_prod_wignerMatrix_apply_eq]
      exact integral_prod_wignerMatrix_apply_eq_zero_of_lt hξm hηm hindep hξzero hηzero
        (Sum.elim w₁ (w₂ ∘ finRotate k)) (Sum.elim (w₁ ∘ finRotate k) w₂)
        (t := x₀) fun y hy ↦ by_contra fun hne ↦ hx₀ ⟨y, hne, by rwa [← hedges y, ← hedges x₀]⟩
    have hzero2 : (∫ ω, wignerWord ξ η w₁ ω ∂P) * star (∫ ω, wignerWord ξ η w₂ ω ∂P) = 0 := by
      dsimp only [wignerWord]
      cases x₀ with
      | inl s₀ =>
        rw [integral_prod_wignerMatrix_apply_eq_zero_of_lt hξm hηm hindep hξzero hηzero
          w₁ (fun s ↦ w₁ (finRotate k s)) (t := s₀) fun s hs ↦ by_contra fun hne ↦
            hx₀ ⟨.inl s, Sum.inl_injective.ne hne, by simpa using hs⟩, zero_mul]
      | inr t₀ =>
        rw [integral_prod_wignerMatrix_apply_eq_zero_of_lt hξm hηm hindep hξzero hηzero
          w₂ (fun t ↦ w₂ (finRotate k t)) (t := t₀) fun t ht ↦ by_contra fun hne ↦
            hx₀ ⟨.inr t, Sum.inr_injective.ne hne, by simpa using ht⟩, star_zero, mul_zero]
    rw [hzero1, hzero2, sub_zero]
  · have hmul := integral_prod_mul_prod_wignerMatrix_apply_eq_mul_integral
      hξm hηm hindep w₁ (fun s ↦ w₁ (finRotate k s)) (fun t ↦ w₂ (finRotate k t)) w₂
      fun s t h ↦ hshare ⟨s, t, by rwa [Sym2.eq_swap (a := w₂ (finRotate k t))] at h⟩
    rw [sub_eq_zero, show star (∫ ω, wignerWord ξ η w₂ ω ∂P) =
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w₂ (finRotate k t)) (w₂ t) ∂P from
      integral_conj.symm.trans (integral_congr_ae (.of_forall fun ω ↦
        star_prod_wignerMatrix_apply ξ η ω w₂ (fun t ↦ w₂ (finRotate k t)))), ← hmul]
    exact integral_congr_ae (.of_forall fun ω ↦
      congrArg (_ * ·) (star_prod_wignerMatrix_apply ξ η ω w₂ fun t ↦ w₂ (finRotate k t)))

section CornerVar

variable {k n : ℕ} {B : ℝ}
  (hindep : iIndepFun
    (fun r ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) P)
  (hξzero : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
  (hηzero : ∀ i, i < n + 1 → ∫ ω, η i ω ∂P = 0)
  (hξp : ∀ ij, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
  (hηp : ∀ i, i < n + 1 → MemLp (η i) (2 * k : ℕ) P)
  (hξ : ∀ ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
  (hη : ∀ i, i < n + 1 → ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
include hindep hξzero hηzero hξp hηp hξ hη

/-- **Variance bound for Wigner empirical spectral moments** (AGZ Lemma 2.1.7). For independent
centered entries on the `(n + 1) × (n + 1)` corner with `2 * k`th absolute moments `≤ B`,
`Var[∫ x ^ k dL_{H_{n+1}}] ≤ 2 * k ^ (2 * k) * B / (n + 1) ^ 2`. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0 (Nat.zero_lt_succ n))
  rcases eq_or_ne k 0 with rfl | hk
  · rw [show (fun ω ↦ ∫ x, x ^ 0 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) = fun _ ↦ 1 from
      funext fun _ ↦ by simp, variance_eq_sub (memLp_const 1)]
    simp only [Pi.pow_apply, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one, sub_self]
    positivity
  · let X ω := ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)
    let T (w : Fin k → Fin (n + 1)) := wignerWord ξ η w
    let covTerm (p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1))) : ℂ :=
      (∫ ω, T p.1 ω * star (T p.2 ω) ∂P) - (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P)
    let G : Finset ((Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1))) :=
      {p | TreeWalk.IsConnectedPair p.1 p.2}
    have hX2 : MemLp X 2 P := memLp_integral_pow_spectralMeasure_wignerMatrix
      (fun ij hij ↦ by simpa [Nat.cast_mul] using hξp ij hij)
      (fun i hi ↦ by simpa [Nat.cast_mul] using hηp i hi)
    have hξpk {ij} (hij : ij.1.2 < n + 1) : MemLp (ξ ij) (k : ℕ) P :=
      (hξp ij hij).mono_exponent (by norm_cast; omega)
    have hηpk {i} (hi : i < n + 1) : MemLp (η i) (k : ℕ) P :=
      (hηp i hi).mono_exponent (by norm_cast; omega)
    have hintT (w : Fin k → Fin (n + 1)) : Integrable (T w) P :=
      memLp_one_iff_integrable.mp (memLp_prod_wignerMatrix_apply
        (fun ij hij ↦ by simpa [Fintype.card_fin] using hξpk hij)
        (fun i hi ↦ by simpa [Fintype.card_fin] using hηpk hi) w (w ∘ finRotate k))
    have hintTT (w₁ w₂ : Fin k → Fin (n + 1)) : Integrable (fun ω ↦ T w₁ ω * star (T w₂ ω)) P := by
      have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by simp [two_mul]
      simp_rw [T, prod_mul_star_prod_wignerMatrix_apply_eq]
      exact memLp_one_iff_integrable.mp (memLp_prod_wignerMatrix_apply
        (fun ij hij ↦ by simpa [hcard] using hξp ij hij)
        (fun i hi ↦ by simpa [hcard] using hηp i hi) _ _)
    have hXeq (ω : Ω) : ((X ω : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ w, T w ω := by
      simpa only [RCLike.ofReal_eq_complex_ofReal, Fintype.card_fin,
        trace_pow_eq_sum_prod _ hk] using Matrix.ofReal_integral_pow_spectralMeasure
          (wignerMatrix ξ η (n + 1) ω) (wignerMatrix_isHermitian ξ η ω (n + 1)) k
    have hvarC := ofReal_variance_eq_mul_sum_cov hX2 (by simp) hXeq hintT hintTT
    have hsumG : (∑ p, covTerm p) = ∑ p ∈ G, covTerm p :=
      (Finset.sum_subset (Finset.subset_univ G) fun p _ hpG ↦
        integral_prod_mul_star_prod_sub_eq_zero_of_not_isConnectedPair
          (fun ij hij ↦ (hξpk hij).aemeasurable) (fun i hi ↦ (hηpk hi).aemeasurable)
          hindep hξzero hηzero (by simpa [G] using hpG)).symm
    have hGcard : (#G : ℝ) ≤ (n + 1 : ℝ) ^ k * (k : ℝ) ^ (2 * k) := by
      simpa [Fintype.card_fin] using
        (Nat.cast_le (α := ℝ)).2 (TreeWalk.card_filter_connectedPair_le (α := Fin (n + 1)) k)
    rw [show Var[X; P] = ‖((Var[X; P] : ℝ) : ℂ)‖ by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (variance_nonneg X P)],
      hvarC, hsumG, norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
    calc (n + 1 : ℝ)⁻¹ ^ 2 * ‖∑ p ∈ G, covTerm p‖
        ≤ (n + 1 : ℝ)⁻¹ ^ 2 * ((#G : ℝ) * (2 * (n + 1 : ℝ)⁻¹ ^ k * B)) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le G covTerm).trans (by
            simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul G _ _ fun p _ ↦
              norm_integral_prod_mul_star_prod_sub_le hk hξp hηp hξ hη p.1 p.2)) (sq_nonneg _)
      _ ≤ (n + 1 : ℝ)⁻¹ ^ 2 *
            (((n + 1 : ℝ) ^ k * (k : ℝ) ^ (2 * k)) * (2 * (n + 1 : ℝ)⁻¹ ^ k * B)) := by gcongr
      _ = 2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
          have h0 : (n + 1 : ℝ) ≠ 0 := by positivity
          field_simp [h0]; simp only [← mul_pow, mul_one_div_cancel h0, one_pow, one_mul]

/-- Chebyshev's tail bound for the `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)`
around its expectation, requiring hypotheses only on the `(n + 1) × (n + 1)` corner. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  refine (meas_ge_le_variance_div_sq (memLp_integral_pow_spectralMeasure_wignerMatrix
    (fun ij hij ↦ by simpa [Nat.cast_mul] using hξp ij hij)
    (fun i hi ↦ by simpa [Nat.cast_mul] using hηp i hi)) hε).trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right
    (variance_integral_pow_spectralMeasure_wignerMatrix_le hindep hξzero hηzero hξp hηp hξ hη)
    (sq_nonneg ε)

end CornerVar

end SingleSpace

section VaryingSpaces

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
  {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {k : ℕ} {B : ℝ}
  (hindep : ∀ n, iIndepFun
    (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) (P n))
  (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
  (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P n = 0)
include hindep hξzero hηzero

private theorem tendsto_expected_of_two_mul
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  exact tendsto_integral_integral_pow_spectralMeasure_wignerMatrix (k := k)
    hindep hξzero hηzero hsecond
    (fun n ij hij ↦ (hξp n ij hij).mono_exponent (by norm_cast; omega))
    (fun n i hi ↦ (hηp n i hi).mono_exponent (by norm_cast; omega))
    (fun n ij hij ↦ MeasureTheory.integral_norm_pow_le_one_add_of_le (by omega)
      (hξp n ij hij) (hξ n ij hij))
    (fun n i hi ↦ MeasureTheory.integral_norm_pow_le_one_add_of_le (by omega)
      (hηp n i hi) (hη n i hi))

/-- Fluctuations of the `k`th empirical spectral moment around its expectation vanish in
probability, including on varying probability spaces. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n|})
      atTop (𝓝 0) :=
  TauCeti.tendsto_measure_abs_ge_of_le_div_add_one_sq fun n ↦
    measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) hε

/-- Convergence in probability of the `k`th empirical spectral moment to the `k`th moment of
`semicircleReal 0 1` on possibly varying probability spaces. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, x ^ k ∂semicircleReal 0 1|}) atTop (𝓝 0) := by
  have hmean := tendsto_expected_of_two_mul hindep hξzero hηzero hsecond hξp hηp hξ hη
  have hfluc := tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    hindep hξzero hηzero hξp hηp hξ hη (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [Metric.tendsto_nhds.1 hmean (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq] at hn; refine measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  let M ω' := ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
    (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)
  linarith [abs_sub_le (M ω) (∫ ω', M ω' ∂P n) (∫ x, x ^ k ∂semicircleReal 0 1)]

end VaryingSpaces

section AlmostSure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section Seq

variable {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
  (hindep : ∀ n, iIndepFun
    (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) (wignerCoordinateIndex (n + 1) r)) P)
  (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P = 0)
  (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P = 0)
include hindep hξzero hηzero

/-- Fluctuations of the `k`th empirical spectral moment around its expectation vanish almost surely
for any sequence of Wigner arrays with independent centered corners and uniformly bounded `2 * k`th
moments. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
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
`semicircleReal 0 1` for a sequence of Wigner arrays `(ξ n, η n)` on `(Ω, P)`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have hmean := tendsto_expected_of_two_mul (P := fun _ ↦ P)
    hindep hξzero hηzero hsecond hξp hηp hξ hη
  filter_upwards [ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    hindep hξzero hηzero hξp hηp hξ hη] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hmean

end Seq

/-- Almost-sure convergence of the `k`th empirical spectral moment to the `k`th moment of
`semicircleReal 0 1` for the corners of a single infinite Wigner array `(ξ, η)`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix
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

end AlmostSure

end VarianceAndConcentration

end TauCeti.Probability
