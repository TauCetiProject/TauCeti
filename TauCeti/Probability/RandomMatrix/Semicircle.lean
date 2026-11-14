/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.WeakConvergence
public import TauCeti.Probability.RandomMatrix.SpectralMoment.Variance

/-!
# Wigner semicircle law under uniformly bounded even moments

Combining the Catalan limit for expected empirical spectral moments with the `O_k(n⁻²)` variance
bound and the compactly supported method of moments yields Wigner's semicircle law whenever each
even absolute entry moment has a finite bound uniform over matrix positions:

* on a single infinite Wigner array `(ξ, η)` with independent coordinates, centered strictly upper
  entries of unit second absolute moment, and uniformly bounded `2k`th entry moments for each `k`,
  the empirical spectral measure of `wignerMatrix ξ η (n + 1)` converges weakly to
  `semicircleReal 0 1` almost surely (`TauCeti.ae_tendsto_spectralMeasure_wignerMatrix`);
* for a triangular array `(ξ n, η n)` on varying probability spaces `(Ω n, P n)` satisfying the
  same row-wise conditions with `n`-uniform `2k`th moment bounds, `∫ f dL_{H_{n+1}}` converges in
  probability to `∫ f d(semicircleReal 0 1)` for every bounded continuous `f : ℝ →ᵇ ℝ`
  (`TauCeti.tendsto_integral_spectralMeasure_wignerMatrix_probability`).

Neither diagonal centering nor identical entry distributions are required, and the moment bound may
depend arbitrarily on the moment order `k`.

## Main results

* `TauCeti.ae_tendsto_integral_pow_spectralMeasure_wignerMatrix`: almost-sure convergence of the
  `k`th empirical spectral moment to `∫ x^k d(semicircleReal 0 1)` under bounded `2k`th moments.
* `TauCeti.ae_tendsto_spectralMeasure_wignerMatrix`: almost-sure weak convergence of empirical
  spectral measures to `semicircleReal 0 1` under uniformly bounded even moments.
* `TauCeti.ae_tendsto_integral_spectralMeasure_wignerMatrix`: almost-sure convergence of all bounded
  continuous linear eigenvalue statistics.
* `TauCeti.tendsto_integral_pow_spectralMeasure_wignerMatrix_probability`: convergence in
  probability of the `k`th empirical spectral moment for triangular Wigner arrays.
* `TauCeti.tendsto_integral_spectralMeasure_wignerMatrix_probability`: convergence in probability of
  bounded continuous spectral integrals to `semicircleReal 0 1` for triangular Wigner arrays.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.2, Theorem 2.1.1 and Lemma 2.1.6-2.1.7.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open TauCeti.Probability
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace TauCeti

private theorem pow_le_one_add_pow_two_mul (x : ℝ) (k : ℕ) :
    x ^ k ≤ 1 + x ^ (2 * k) := by
  have hsq : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [mul_comm, pow_mul]
  nlinarith [sq_nonneg (x ^ k - 1)]

private theorem integral_norm_pow_le_one_add {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [NormedAddCommGroup E] {f : Ω → E} {k : ℕ} {B : ℝ}
    (hf : MemLp f (2 * k : ℕ) P) (hb : ∫ ω, ‖f ω‖ ^ (2 * k) ∂P ≤ B) :
    ∫ ω, ‖f ω‖ ^ k ∂P ≤ 1 + B := by
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (f ω)) _).trans hb
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hB
  · have hfk : MemLp f k P :=
      hf.mono_exponent (by norm_cast; exact Nat.le_mul_of_pos_left k two_pos)
    have hi1 : Integrable (fun ω ↦ ‖f ω‖ ^ k) P := hfk.integrable_norm_pow hk
    have hi2 : Integrable (fun ω ↦ ‖f ω‖ ^ (2 * k)) P := hf.integrable_norm_pow (by positivity)
    calc
      ∫ ω, ‖f ω‖ ^ k ∂P ≤ ∫ ω, (1 + ‖f ω‖ ^ (2 * k)) ∂P :=
        integral_mono hi1 ((integrable_const 1).add hi2) fun ω ↦
          pow_le_one_add_pow_two_mul ‖f ω‖ k
      _ = 1 + ∫ ω, ‖f ω‖ ^ (2 * k) ∂P := by
        rw [integral_add (integrable_const 1) hi2, integral_const, probReal_univ, one_smul]
      _ ≤ 1 + B := add_le_add_right hb 1

private theorem integrable_spectralMeasure {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Integrable f (A.spectralMeasure hA : Measure ℝ) := by
  rw [Matrix.spectralMeasure_def, empiricalMeasureOfFintype_toMeasure,
    integrable_finsetSum_measure]
  exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)

section FixedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- **Almost-sure convergence of a single Wigner spectral moment.** On an infinite Wigner array with
independent coordinates, centered strictly upper entries of unit second absolute moment, and `2k`th
absolute moments bounded by `B`, the `k`th empirical spectral moment converges almost surely to
`∫ x^k d(semicircleReal 0 1)`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have := hindep.isProbabilityMeasure
  have hle : (k : ℝ≥0∞) ≤ (2 * k : ℕ) := by norm_cast; exact Nat.le_mul_of_pos_left k two_pos
  have hmean := tendsto_integral_pow_spectralMeasure_wignerMatrix
    (P := fun _ ↦ P) (ξ := fun _ ↦ ξ) (η := fun _ ↦ η) (k := k) (B := 1 + B)
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hsecond)
    (fun _ ij ↦ (hξp ij).mono_exponent hle) (fun _ i ↦ (hηp i).mono_exponent hle)
    (fun _ ij ↦ integral_norm_pow_le_one_add (hξp ij) (hξ ij))
    (fun _ i ↦ integral_norm_pow_le_one_add (hηp i) (hη i))
  filter_upwards [ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    hindep hξzero hξp hηp hξ hη] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hmean

/-- **Almost-sure Wigner semicircle law under uniformly bounded even moments.** On a single infinite
Wigner array with independent coordinates, centered strictly upper entries of unit second absolute
moment, and position-uniform bounds on the `2k`th absolute entry moments for every `k : ℕ`, the
empirical spectral measure of `wignerMatrix ξ η (n + 1)` converges weakly to `semicircleReal 0 1`
almost surely. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ (k : ℕ) ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ (k : ℕ) i, MemLp (η i) (2 * k : ℕ) P)
    (hbound : ∀ k : ℕ, ∃ B : ℝ,
      (∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) ∧ ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 1, inferInstance⟩) := by
  have hall : ∀ k : ℕ, ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := fun k ↦ by
    obtain ⟨B, hξB, hηB⟩ := hbound k
    exact ae_tendsto_integral_pow_spectralMeasure_wignerMatrix
      hindep hξzero hsecond (hξp k) (hηp k) hξB hηB
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  exact ProbabilityMeasure.tendsto_of_tendsto_integral_pow isCompact_Icc
    (ae_iff.mp (ae_mem_Icc_semicircleReal 0 1))
    (fun k ↦ Eventually.of_forall fun n ↦ integrable_spectralMeasure _ _ _) hω

/-- Almost surely, integrating any bounded continuous test function against the empirical spectral
measure of `wignerMatrix ξ η (n + 1)` converges to its integral against `semicircleReal 0 1`. -/
theorem ae_tendsto_integral_spectralMeasure_wignerMatrix
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ (k : ℕ) ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ (k : ℕ) i, MemLp (η i) (2 * k : ℕ) P)
    (hbound : ∀ k : ℕ, ∃ B : ℝ,
      (∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) ∧ ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n ↦
      ∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, f x ∂semicircleReal 0 1)) := by
  filter_upwards [ae_tendsto_spectralMeasure_wignerMatrix
    hindep hξzero hsecond hξp hηp hbound] with ω hω
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hω

end FixedSpace

section TriangularArray

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
  {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}

/-- **Convergence in probability of a single Wigner spectral moment for triangular arrays.** Under
row-wise coordinate independence, off-diagonal centering, unit off-diagonal second absolute moments,
and uniformly bounded `2k`th moments, the `k`th empirical spectral moment converges in probability
to `∫ x^k d(semicircleReal 0 1)`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_probability {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
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
  have _ (n : ℕ) := (hindep n).isProbabilityMeasure
  have hle : (k : ℝ≥0∞) ≤ (2 * k : ℕ) := by norm_cast; exact Nat.le_mul_of_pos_left k two_pos
  have hmean := tendsto_integral_pow_spectralMeasure_wignerMatrix (B := 1 + B) hindep hξzero hsecond
    (fun n ij ↦ (hξp n ij).mono_exponent hle) (fun n i ↦ (hηp n i).mono_exponent hle)
    (fun n ij ↦ integral_norm_pow_le_one_add (hξp n ij) (hξ n ij))
    (fun n i ↦ integral_norm_pow_le_one_add (hηp n i) (hη n i))
  have hfluc := tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    hindep hξzero hξp hηp hξ hη (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [Metric.tendsto_nhds.mp hmean (ε / 2) (half_pos hε)] with n hn
  refine measure_mono fun ω hω ↦ ?_
  rw [Real.dist_eq] at hn
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith [abs_sub_le
    (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
    (∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n)
    (∫ x, x ^ k ∂semicircleReal 0 1)]

/-- **Triangular-array Wigner semicircle law in probability under bounded even moments.** When a
triangular Wigner array has row-wise independent coordinates, centered strictly upper entries of
unit second absolute moment, and `(n, i, j)`-uniform bounds on the `2k`th absolute entry moments for
every `k : ℕ`, `∫ f dL_{H_{n+1}}` converges in probability to `∫ f d(semicircleReal 0 1)` for every
bounded continuous function `f : ℝ →ᵇ ℝ`. -/
theorem tendsto_integral_spectralMeasure_wignerMatrix_probability
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ (k : ℕ) n ij, MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ (k : ℕ) n i, MemLp (η n i) (2 * k : ℕ) (P n))
    (hbound : ∀ k : ℕ, ∃ B : ℝ,
      (∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B) ∧
        ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, f x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, f x ∂semicircleReal 0 1|})
      atTop (𝓝 0) :=
  ProbabilityMeasure.tendsto_measure_ge_of_tendsto_integral_pow
    (μ := ⟨semicircleReal 0 1, inferInstance⟩)
    isCompact_Icc (ae_iff.mp (ae_mem_Icc_semicircleReal 0 1))
    (fun _ ↦ Eventually.of_forall fun _ ↦ Eventually.of_forall fun _ ↦
      integrable_spectralMeasure _ _ _)
    (fun k _ hδ ↦ by
      obtain ⟨B, hξB, hηB⟩ := hbound k
      exact tendsto_integral_pow_spectralMeasure_wignerMatrix_probability
        hindep hξzero hsecond (hξp k) (hηp k) hξB hηB hδ)
    f hε

end TriangularArray

end TauCeti
