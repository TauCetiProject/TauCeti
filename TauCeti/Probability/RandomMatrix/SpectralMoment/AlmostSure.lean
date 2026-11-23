/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SpectralMoment.Second
public import TauCeti.Probability.RandomMatrix.SpectralMoment.Variance
import Mathlib.Analysis.PSeries

/-!
# Almost-sure convergence of Wigner spectral moments

Summability of `∑ (n + 1)⁻²` applied to the `O((n + 1)⁻²)` variance bounds gives almost-sure
convergence of empirical spectral moment fluctuations to zero via the Borel--Cantelli lemma
(`ae_tendsto_sub_integral_of_summable_variance`).

For the second empirical spectral moment, only pairwise independence of squared coordinate norms
with uniformly bounded variances is needed, with no independence between matrices of different
sizes. For unit off-diagonal second absolute moments and a common diagonal second moment, the mean
tends to one, so the second empirical spectral moment tends almost surely to one.

For general order `k`, under independent centered entries in `L^(2k)` with uniformly bounded
`2k`-th absolute moments, the `O((n + 1)⁻²)` variance bound from
`TauCeti.Probability.RandomMatrix.SpectralMoment.Variance` gives almost-sure vanishing of all
empirical spectral moment fluctuations (and simultaneously for all `k` when every even moment is
uniformly bounded). Combined with the `O((n + 1)⁻¹/²)` expected odd-moment bound, every odd
empirical spectral moment converges almost surely to zero.

## Main results

* `ae_tendsto_second_spectralMoment_sub_mean` and `ae_tendsto_second_spectralMoment`: almost-sure
  concentration and convergence to one of the second empirical spectral moment under pairwise
  independence of squared coordinate norms.
* `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean` and
  `ae_forall_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean`: almost-sure vanishing of
  empirical spectral moment fluctuations of general order via Borel--Cantelli.
* `ae_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix` and
  `ae_forall_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix`: almost-sure
  convergence of odd empirical spectral moments to zero.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §2.1, §2.1.4 Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.4.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology ENNReal

namespace TauCeti.Probability

section SecondMoment

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Second spectral moment fluctuations tend almost surely to zero under the summable
variance bound. Pairwise independence is imposed within each finite coordinate family. -/
theorem ae_tendsto_second_spectralMoment_sub_mean {V : ℝ}
    (hindep : ∀ n, Pairwise fun i j ↦
      IndepFun (wignerCoordinateSquare ξ η (n + 1) i)
        (wignerCoordinateSquare ξ η (n + 1) j) P)
    (hmem : ∀ n i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ n i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) := by
  have hmem' (n : ℕ) : MemLp (fun ω ↦ ∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P := by
    simp_rw [integral_sq_spectralMeasure_wignerMatrix_weighted]
    exact memLp_finsetSum Finset.univ fun i _ ↦ (hmem n i).const_mul _
  have hs : Summable fun n : ℕ ↦ 8 * V / (n + 1 : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
      ((summable_nat_add_iff 1).2
        ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))).mul_left (8 * V)
  have hvar' : Summable fun n ↦ Var[fun ω ↦ ∫ x, x ^ 2
      ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] :=
    Summable.of_nonneg_of_le (fun n ↦ variance_nonneg _ _)
      (fun n ↦ variance_second_spectralMoment_le n (hindep n) (hmem n) (hvar n)) hs
  exact ae_tendsto_sub_integral_of_summable_variance hmem' hvar'

/-- With unit off-diagonal second absolute moments and constant diagonal second moment,
the second empirical spectral moment tends almost surely to one. Square-integrable squared
norms with uniformly bounded variances and pairwise independence of those squares suffice;
neither centering nor identical distribution of the entries is required. -/
theorem ae_tendsto_second_spectralMoment {V σ2 : ℝ}
    (hindep : ∀ n, Pairwise fun i j ↦
      IndepFun (wignerCoordinateSquare ξ η (n + 1) i)
        (wignerCoordinateSquare ξ η (n + 1) j) P)
    (hmem : ∀ n i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ n i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hη : ∀ i, ∫ ω, η i ω ^ 2 ∂P = σ2) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) atTop (𝓝 1) := by
  have hmean (n : ℕ) :
      (∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) =
        1 + (σ2 - 1) * (n + 1 : ℝ)⁻¹ := by
    have hξi : ∀ ij, Integrable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P := fun ij ↦
      Integrable.of_integral_ne_zero (by rw [hξ ij]; exact one_ne_zero)
    have hηi (i : ℕ) : Integrable (fun ω ↦ η i ω ^ 2) P := by
      exact ((hmem i (.inr ⟨i, Nat.lt_succ_self i⟩)).integrable (by norm_num)).congr
        (ae_of_all P (fun ω ↦ wignerCoordinateSquare_inr (i + 1) ⟨i, Nat.lt_succ_self i⟩ ω))
    have h := integral_re_trace_wignerMatrix_mul_self hξi hξ hηi hη (n + 1)
    have heq (ω : Ω) :
        (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
        (((n + 1 : ℕ) : ℂ)⁻¹ *
          (wignerMatrix ξ η (n + 1) ω * wignerMatrix ξ η (n + 1) ω).trace).re := by
      rw [Matrix.integral_pow_spectralMeasure]
      simp only [pow_two, Fintype.card_fin, RCLike.re_to_complex]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simp_rw [heq]
    rw [h]
    push_cast
    field_simp
    ring
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hm : Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ 2
      ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) atTop (𝓝 1) := by
    simp_rw [hmean]
    simpa using tendsto_const_nhds.add (hinv.const_mul (σ2 - 1))
  filter_upwards [ae_tendsto_second_spectralMoment_sub_mean hindep hmem hvar] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hm

end SecondMoment

section GeneralOrder

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- **Almost-sure vanishing of empirical spectral moment fluctuations.** If the entries of the
Wigner array are independent, centered, in `L^(2k)`, and have `2k`-th absolute moments uniformly
bounded by `B`, then the `k`-th empirical spectral moment minus its expectation converges almost
surely to zero as `n → ∞`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
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
  have := hindep.isProbabilityMeasure
  have hmem (n : ℕ) : MemLp (fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P :=
    memLp_integral_pow_spectralMeasure_wignerMatrix (p := 2) (fun _ ↦ inferInstance) n
      (fun ij _ ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hξp ij)
      (fun i _ ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hηp i)
  have hs : Summable fun n : ℕ ↦ 2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
      ((summable_nat_add_iff 1).2
        ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))).mul_left
          (2 * (k : ℝ) ^ (2 * k) * B)
  have hvar : Summable fun n ↦ Var[fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] :=
    Summable.of_nonneg_of_le (fun n ↦ variance_nonneg _ _)
      (fun n ↦ variance_integral_pow_spectralMeasure_wignerMatrix_le
        hindep hξzero hηzero hξp hηp hξ hη n) hs
  exact ae_tendsto_sub_integral_of_summable_variance hmem hvar

/-- **Simultaneous almost-sure vanishing of all empirical spectral moment fluctuations.** When every
even moment order `2k` of the independent centered entries is uniformly bounded across the array by
`B k`, on a single full-measure event the fluctuations of all empirical spectral moments around
their expectations vanish as `n → ∞`. -/
theorem ae_forall_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
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

/-- **Almost-sure convergence of odd empirical spectral moments to zero.** Under independent
centered entries in `L^(4m + 2)` with `(4m + 2)`-th absolute moments uniformly bounded by `B`, the
`(2m + 1)`-st empirical spectral moment of `Hₙ₊₁` converges almost surely to zero as `n → ∞`. -/
theorem ae_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
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
  have := hindep.isProbabilityMeasure
  have hle : ((2 * m + 1 : ℕ) : ℝ≥0∞) ≤ (2 * (2 * m + 1) : ℕ) := by exact_mod_cast (by omega)
  have hmean := tendsto_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hηzero)
    (fun _ ij ↦ (hξp ij).mono_exponent hle) (fun _ i ↦ (hηp i).mono_exponent hle)
    (fun _ ij ↦ (hξp ij).integral_norm_pow_le_sqrt_integral_norm_pow_two_mul.trans
      (Real.sqrt_le_sqrt (hξ ij)))
    (fun _ i ↦ (hηp i).integral_norm_pow_le_sqrt_integral_norm_pow_two_mul.trans
      (Real.sqrt_le_sqrt (hη i)))
  filter_upwards [ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    hindep hξzero hηzero hξp hηp hξ hη] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hmean

/-- **Simultaneous almost-sure convergence of all odd empirical spectral moments to zero.** When
every `(4m + 2)`-th absolute moment of the independent centered entries is uniformly bounded by
`B m`, on a single full-measure event all odd empirical spectral moments converge to zero. -/
theorem ae_forall_tendsto_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix
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

end GeneralOrder

end TauCeti.Probability
