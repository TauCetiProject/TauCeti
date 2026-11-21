/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SpectralMoment.Expected
public import TauCeti.Probability.RandomMatrix.SpectralMoment.Variance
public import TauCeti.Probability.RandomMatrix.SpectralMoment.AlmostSure
import Mathlib.Analysis.PSeries
import TauCeti.Probability.Independence.Basic
import TauCeti.Probability.Moments.Variance

/-!
# Moment convergence of Wigner empirical spectral measures

Combining the quantitative expected-moment convergence from
`TauCeti.Probability.RandomMatrix.SpectralMoment.Expected` with the `O((n + 1)⁻²)` trace
variance bounds from `TauCeti.Probability.RandomMatrix.SpectralMoment.Variance`, this file derives
both convergence in probability (on possibly varying probability spaces) and almost-sure convergence
(for a sequence of independent-corner Wigner arrays as well as for a single infinite array) of every
`k`-th empirical spectral moment to the `k`-th moment of `semicircleReal 0 s`.

## Main results

* `tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability`:
  convergence in probability of the `k`-th empirical spectral moment to
  `∫ x, x ^ k ∂semicircleReal 0 s` on possibly varying probability spaces under corner-local
  independence and uniform `2k`-th moment bounds.
* `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq`,
  `ae_tendsto_integral_pow_spectralMeasure_wignerMatrix`, and
  `ae_forall_tendsto_integral_pow_spectralMeasure_wignerMatrix`: almost-sure convergence of
  empirical spectral moments to `∫ x, x ^ k ∂semicircleReal 0 s` for a sequence of Wigner arrays
  (with no independence assumed across `n`) and for a single infinite array.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3–§2.1.4, Lemmas 2.1.6 and 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability

section CornerHelpers

private def padZeroOffDiag {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (n : ℕ) :
    StrictUpper → Ω → ℂ :=
  fun ij ω ↦ if ij.val.2 < n then ξ ij ω else 0

private def padZeroDiag {Ω : Type*} (η : ℕ → Ω → ℝ) (n : ℕ) : ℕ → Ω → ℝ :=
  fun i ω ↦ if i < n then η i ω else 0

private theorem padZeroOffDiag_of_lt {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) {n : ℕ}
    {ij : StrictUpper} (h : ij.val.2 < n) : padZeroOffDiag ξ n ij = ξ ij := by
  ext ω; simp [padZeroOffDiag, h]

private theorem padZeroOffDiag_of_not_lt {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) {n : ℕ}
    {ij : StrictUpper} (h : ¬ ij.val.2 < n) : padZeroOffDiag ξ n ij = 0 := by
  ext ω; simp [padZeroOffDiag, h]

private theorem padZeroDiag_of_lt {Ω : Type*} (η : ℕ → Ω → ℝ) {n : ℕ} {i : ℕ} (h : i < n) :
    padZeroDiag η n i = η i := by
  ext ω; simp [padZeroDiag, h]

private theorem padZeroDiag_of_not_lt {Ω : Type*} (η : ℕ → Ω → ℝ) {n : ℕ} {i : ℕ} (h : ¬ i < n) :
    padZeroDiag η n i = 0 := by
  ext ω; simp [padZeroDiag, h]

private theorem wignerMatrix_padZero_eq {Ω : Type*} (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    wignerMatrix (padZeroOffDiag ξ n) (padZeroDiag η n) n ω = wignerMatrix ξ η n ω :=
  wignerMatrix_congr ω (fun ij hij ↦ by simp [padZeroOffDiag, hij])
    (fun i hi ↦ by simp [padZeroDiag, hi])

private theorem iIndepFun_padZero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P) :
    iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (padZeroOffDiag ξ n) (fun i ω ↦ (padZeroDiag η n i ω : ℂ)) idx) P := by
  have := hindep.isProbabilityMeasure
  let e : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} → StrictUpper ⊕ ℕ :=
    Sum.map Subtype.val Subtype.val
  refine iIndepFun_of_ae_eq_const_outside_range (e := e) ?_ ?_
  · refine hindep.congr fun r ↦ .of_forall fun ω ↦ ?_
    rcases r with ⟨ij, hij⟩ | ⟨i, hi⟩
    · simp [e, padZeroOffDiag, hij]
    · simp [e, padZeroDiag, hi]
  · intro idx hnot
    refine ⟨0, .of_forall fun ω ↦ ?_⟩
    rcases idx with ij | i
    · have hij : ¬ ij.val.2 < n := fun h ↦ hnot ⟨.inl ⟨ij, h⟩, rfl⟩
      simp [padZeroOffDiag, hij]
    · have hi : ¬ i < n := fun h ↦ hnot ⟨.inr ⟨i, h⟩, rfl⟩
      simp [padZeroDiag, hi]

private theorem variance_integral_pow_spectralMeasure_wignerMatrix_le_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} {B : ℝ}
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
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans
      (hη 0 (Nat.zero_lt_succ n))
  have h0B : ∫ _ω : Ω, (0 : ℝ) ^ (2 * k) ∂P ≤ B := by
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using hη 0 (Nat.zero_lt_succ n)
    · simpa [hk] using hB
  have hvar := variance_integral_pow_spectralMeasure_wignerMatrix_le
    (ξ := padZeroOffDiag ξ (n + 1)) (η := padZeroDiag η (n + 1)) (k := k) (B := B)
    (iIndepFun_padZero hindep)
    (fun ij ↦ by by_cases h : ij.val.2 < n + 1 <;> simp [padZeroOffDiag, h, hξzero])
    (fun i ↦ by by_cases h : i < n + 1 <;> simp [padZeroDiag, h, hηzero])
    (fun ij ↦ by
      by_cases h : ij.val.2 < n + 1
      · rw [padZeroOffDiag_of_lt _ h]; exact hξp ij h
      · rw [padZeroOffDiag_of_not_lt _ h]; exact MemLp.zero)
    (fun i ↦ by
      by_cases h : i < n + 1
      · rw [padZeroDiag_of_lt _ h]; exact hηp i h
      · rw [padZeroDiag_of_not_lt _ h]; exact MemLp.zero)
    (fun ij ↦ by
      by_cases h : ij.val.2 < n + 1
      · simpa [padZeroOffDiag, h] using hξ ij h
      · simpa [padZeroOffDiag, h] using h0B)
    (fun i ↦ by
      by_cases h : i < n + 1
      · simpa [padZeroDiag, h] using hη i h
      · simpa [padZeroDiag, h] using h0B) n
  simp_rw [wignerMatrix_padZero_eq] at hvar
  exact hvar

private theorem memLp_integral_pow_spectralMeasure_wignerMatrix_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (2 * k : ℕ) P) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P := by
  have hm := memLp_integral_pow_spectralMeasure_wignerMatrix (p := 2) (k := k)
    (ξ := padZeroOffDiag ξ (n + 1)) (η := padZeroDiag η (n + 1))
    (fun ij ↦ by
      by_cases h : ij.val.2 < n + 1
      · rw [padZeroOffDiag_of_lt _ h]; exact_mod_cast hξp ij h
      · rw [padZeroOffDiag_of_not_lt _ h]; exact MemLp.zero)
    (fun i ↦ by
      by_cases h : i < n + 1
      · rw [padZeroDiag_of_lt _ h]; exact_mod_cast hηp i h
      · rw [padZeroDiag_of_not_lt _ h]; exact MemLp.zero) n
  simp_rw [wignerMatrix_padZero_eq] at hm
  exact hm

end CornerHelpers

section VaryingSpaces

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
  {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
  {k : ℕ} {B : ℝ} {s : ℝ≥0}
  (hindep : ∀ n, iIndepFun
    (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
      Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
  (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
  (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P n = 0)
include hindep hξzero hηzero

private theorem tendsto_expected_of_two_mul
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 s)) := by
  have (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hle : (k : ℝ≥0∞) ≤ (2 * k : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_left k two_pos
  exact tendsto_integral_integral_pow_spectralMeasure_wignerMatrix' (k := k) (B := √B) (s := s)
    hindep hξzero hηzero
    (fun n ij hij ↦ (hξp n ij hij).mono_exponent hle)
    (fun n i hi ↦ (hηp n i hi).mono_exponent hle)
    (fun n ij hij ↦
      (hξp n ij hij).integral_norm_pow_le_sqrt_integral_norm_pow_two_mul.trans
        (Real.sqrt_le_sqrt (hξ n ij hij)))
    (fun n i hi ↦
      (hηp n i hi).integral_norm_pow_le_sqrt_integral_norm_pow_two_mul.trans
        (Real.sqrt_le_sqrt (hη n i hi)))
    hξsq

/-- **Convergence in probability of empirical spectral moments.** On possibly varying probability
spaces, under corner-local independence, unit-or-common variance `s`, and uniform `2k`-th moment
bounds, the `k`-th empirical spectral moment converges in probability to the `k`-th moment of
`semicircleReal 0 s`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
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
  have hmean := tendsto_expected_of_two_mul hindep hξzero hηzero hξsq hξp hηp hξ hη
  have hmem (n : ℕ) : MemLp (fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) 2 (P n) :=
    memLp_integral_pow_spectralMeasure_wignerMatrix_of_lt (hξp n) (hηp n)
  have hvar : Tendsto (fun n ↦ Var[fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ); P n]) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ variance_nonneg _ _)
      (fun n ↦ variance_integral_pow_spectralMeasure_wignerMatrix_le_of_lt
        (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n))
      (by
        simpa using tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop two_ne_zero).comp
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)))
  have hfluc := tendsto_measure_abs_sub_integral_ge_of_tendsto_variance hmem hvar (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [Metric.tendsto_nhds.1 hmean (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq] at hn
  refine measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  let M ω' := ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
    (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)
  linarith [abs_sub_le (M ω) (∫ ω', M ω' ∂P n) (∫ x, x ^ k ∂semicircleReal 0 s)]

end VaryingSpaces

section AlmostSure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section Seq

variable {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ} {k : ℕ} {B : ℝ} {s : ℝ≥0}
  (hindep : ∀ n, iIndepFun
    (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
      Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) P)
  (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P = 0)
  (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P = 0)
include hindep hξzero hηzero

/-- **Almost-sure convergence of empirical spectral moments for a sequence of Wigner arrays.**
With no independence assumed across `n`, under corner-local independence, centered entries,
off-diagonal second absolute moment `s`, and uniformly bounded `2k`-th moments, the `k`-th
empirical spectral moment converges almost surely to `∫ x, x ^ k ∂semicircleReal 0 s`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P = s)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 s)) := by
  have := (hindep 0).isProbabilityMeasure
  have hmean := tendsto_expected_of_two_mul (P := fun _ ↦ P)
    hindep hξzero hηzero hξsq hξp hηp hξ hη
  have hmem (n : ℕ) : MemLp (fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) 2 P :=
    memLp_integral_pow_spectralMeasure_wignerMatrix_of_lt (hξp n) (hηp n)
  have hs : Summable fun n : ℕ ↦ 2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
      ((summable_nat_add_iff 1).2
        ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))).mul_left
          (2 * (k : ℝ) ^ (2 * k) * B)
  have hvar : Summable fun n ↦ Var[fun ω ↦ ∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ); P] :=
    Summable.of_nonneg_of_le (fun n ↦ variance_nonneg _ _)
      (fun n ↦ variance_integral_pow_spectralMeasure_wignerMatrix_le_of_lt
        (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n)) hs
  filter_upwards [ae_tendsto_sub_integral_of_summable_variance hmem hvar] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hmean

end Seq

/-- **Almost-sure convergence of empirical spectral moments for an infinite Wigner array.**
Under independent centered entries, off-diagonal second absolute moment `s`, and uniformly bounded
`2k`-th absolute moments, the `k`-th empirical spectral moment converges almost surely to
`∫ x, x ^ k ∂semicircleReal 0 s`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 s)) :=
  ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
    (fun _ ↦ iIndepFun_sumElim_ofReal_subtype_lt hindep)
    (fun _ ij _ ↦ hξzero ij) (fun _ i _ ↦ hηzero i) (fun _ ij _ ↦ hξsq ij)
    (fun _ ij _ ↦ hξp ij) (fun _ i _ ↦ hηp i) (fun _ ij _ ↦ hξ ij) (fun _ i _ ↦ hη i)

/-- **Simultaneous almost-sure convergence of all empirical spectral moments.** When every even
moment order `2k` of the independent centered entries is uniformly bounded by `B k` and the
off-diagonal entries have common second absolute moment `s`, on a single full-measure event every
`k`-th empirical spectral moment converges to `∫ x, x ^ k ∂semicircleReal 0 s`. -/
theorem ae_forall_tendsto_integral_pow_spectralMeasure_wignerMatrix
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {B : ℕ → ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s)
    (hξp : ∀ k ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ k i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ k ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B k)
    (hη : ∀ k i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B k) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 s)) :=
  ae_all_iff.2 fun k ↦ ae_tendsto_integral_pow_spectralMeasure_wignerMatrix
    hindep hξzero hηzero hξsq (hξp k) (hηp k) (hξ k) (hη k)

end AlmostSure

end TauCeti.Probability
