/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SpectralMoment.Moments
public import TauCeti.Probability.Moments.WeakConvergence
public import Mathlib.Probability.IdentDistrib

/-!
# Wigner's semicircle law under uniform moment bounds

Combining spectral-moment convergence (`TauCeti.Probability.RandomMatrix.SpectralMoment.Moments`)
with the compact-support method of moments (`ProbabilityMeasure.tendsto_of_tendsto_integral_pow`
and `ProbabilityMeasure.tendsto_measure_abs_integral_sub_ge_of_isCompact`), we prove Wigner's
semicircle law almost surely and in probability for `(n + 1) × (n + 1)` Hermitian Wigner matrices
with uniformly bounded even moments, without assuming identically distributed entries or
independence across matrix sizes.

## Main results

* `ae_tendsto_spectralMeasure_wignerMatrix_of_seq`, `ae_tendsto_spectralMeasure_wignerMatrix`,
  and `ae_tendsto_spectralMeasure_wignerMatrix_of_identDistrib`: almost-sure weak convergence to
  `semicircleReal 0 s`.
* `tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability` and
  `tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability_of_identDistrib`:
  convergence in probability of bounded continuous linear statistics on varying probability spaces.

## References

* E. P. Wigner, *Characteristic vectors of bordered matrices with infinite dimensions*,
  Ann. of Math. (2) **62** (1955), 548–564.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.1–§2.1.3, Theorem 2.1.1 (via Lemmas 2.1.6 and 2.1.7).
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.Probability

private theorem semicircleReal_compl_Icc_eq_zero (s : ℝ≥0) :
    (semicircleReal 0 s)
      (Set.Icc ((0 : ℝ) - 2 * Real.sqrt s) ((0 : ℝ) + 2 * Real.sqrt s))ᶜ = 0 :=
  ae_iff.mp (ae_mem_Icc_semicircleReal 0 s)

/-- **Wigner's semicircle law (almost surely, sequence of arrays).** Empirical spectral measures of
`(n + 1) × (n + 1)` Wigner matrices with centered entries whose diagonal and strictly
upper-triangular entries are jointly independent within each corner, off-diagonal second absolute
moment `s`, and uniformly bounded even moments converge weakly a.s. to `semicircleReal 0 s`,
without assuming independence across matrix sizes or identically distributed entries. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_of_seq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) P)
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P = 0)
    (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P = 0)
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P = s)
    (hξp : ∀ k n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ k n, ∀ i < n + 1, MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ k, ∃ B, ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ k, ∃ B, ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 s, inferInstance⟩) := by
  have hae (k : ℕ) :=
    let ⟨B₁, hB₁⟩ := hξ k; let ⟨B₂, hB₂⟩ := hη k
    ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq hindep hξzero hηzero hξsq
      (hξp k) (hηp k) (fun n ij hij ↦ (hB₁ n ij hij).trans (le_max_left B₁ B₂))
      (fun n i hi ↦ (hB₂ n i hi).trans (le_max_right B₁ B₂))
  filter_upwards [ae_all_iff.2 hae] with ω hω
  exact ProbabilityMeasure.tendsto_of_tendsto_integral_pow
    isCompact_Icc (semicircleReal_compl_Icc_eq_zero s)
    (fun k ↦ Eventually.of_forall fun _ ↦ Matrix.integrable_pow_spectralMeasure _ _ k) hω

/-- **Wigner's semicircle law (almost surely, infinite array).** Empirical spectral measures of the
corners of an infinite Wigner array with independent centered entries, off-diagonal second moment
`s`, and uniformly bounded even moments converge weakly a.s. to `semicircleReal 0 s`. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s)
    (hξp : ∀ k ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ k i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ k, ∃ B, ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ k, ∃ B, ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 s, inferInstance⟩) :=
  ae_tendsto_spectralMeasure_wignerMatrix_of_seq
    (fun _ ↦ iIndepFun_sumElim_ofReal_subtype_lt hindep)
    (fun _ ij _ ↦ hξzero ij) (fun _ i _ ↦ hηzero i) (fun _ ij _ ↦ hξsq ij)
    (fun k _ ij _ ↦ hξp k ij) (fun k _ i _ ↦ hηp k i)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ij _ ↦ hB ij⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ i _ ↦ hB i⟩)

/-- **Wigner's semicircle law (almost surely, identically distributed entries).** Specialization of
`ae_tendsto_spectralMeasure_wignerMatrix` to entries identically distributed with `ξ₀` and `η₀`. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_of_identDistrib
    {Ω Ω₀ Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    {P : Measure Ω} {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {ξ₀ : Ω₀ → ℂ} {η₀ : Ω₁ → ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξid : ∀ ij, IdentDistrib (ξ ij) ξ₀ P P₀) (hηid : ∀ i, IdentDistrib (η i) η₀ P P₁)
    (hξzero : ∫ ω, ξ₀ ω ∂P₀ = 0) (hηzero : ∫ ω, η₀ ω ∂P₁ = 0)
    (hξsq : ∫ ω, ‖ξ₀ ω‖ ^ 2 ∂P₀ = s)
    (hξp : ∀ k : ℕ, MemLp ξ₀ (2 * k : ℕ) P₀) (hηp : ∀ k : ℕ, MemLp η₀ (2 * k : ℕ) P₁) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 s, inferInstance⟩) :=
  ae_tendsto_spectralMeasure_wignerMatrix hindep
    (fun ij ↦ (hξid ij).integral_eq.trans hξzero) (fun i ↦ (hηid i).integral_eq.trans hηzero)
    (fun ij ↦ (hξid ij).norm.sq.integral_eq.trans hξsq)
    (fun k ij ↦ (hξid ij).memLp_iff.mpr (hξp k)) (fun k i ↦ (hηid i).memLp_iff.mpr (hηp k))
    (fun _ ↦ ⟨_, fun ij ↦ (hξid ij).norm.pow.integral_eq.le⟩)
    (fun _ ↦ ⟨_, fun i ↦ (hηid i).norm.pow.integral_eq.le⟩)

/-- **Wigner's semicircle law (in probability).** On possibly varying probability spaces, bounded
continuous linear statistics `f : ℝ →ᵇ ℝ` of `(n + 1) × (n + 1)` Wigner empirical spectral measures
converge in probability to `∫ x, f x ∂semicircleReal 0 s`. -/
theorem tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P n = 0)
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s)
    (hξp : ∀ k n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ k n, ∀ i < n + 1, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n (ij : StrictUpper), ij.val.2 < n + 1 →
      ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, f x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, f x ∂semicircleReal 0 s|}) atTop (𝓝 0) :=
  ProbabilityMeasure.tendsto_measure_abs_integral_sub_ge_of_isCompact
    (ν := fun n ω ↦ (wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)))
    ⟨semicircleReal 0 s, inferInstance⟩ isCompact_Icc (semicircleReal_compl_Icc_eq_zero s)
    (Eventually.of_forall fun _ ↦ .of_forall fun _ k ↦ Matrix.integrable_pow_spectralMeasure _ _ k)
    (fun k {_} hη_pos ↦
      let ⟨B₁, hB₁⟩ := hξ k; let ⟨B₂, hB₂⟩ := hη k
      tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
        hindep hξzero hηzero hξsq (hξp k) (hηp k)
        (fun n ij hij ↦ (hB₁ n ij hij).trans (le_max_left B₁ B₂))
        (fun n i hi ↦ (hB₂ n i hi).trans (le_max_right B₁ B₂)) hη_pos)
    f hε

/-- **Wigner's semicircle law (in probability, identically distributed entries).** Specialization of
`tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability` to `ξ₀` and `η₀`. -/
theorem tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability_of_identDistrib
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {Ω₀ Ω₁ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {ξ₀ : Ω₀ → ℂ} {η₀ : Ω₁ → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξid : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → IdentDistrib (ξ n ij) ξ₀ (P n) P₀)
    (hηid : ∀ n, ∀ i < n + 1, IdentDistrib (η n i) η₀ (P n) P₁)
    (hξzero : ∫ ω, ξ₀ ω ∂P₀ = 0) (hηzero : ∫ ω, η₀ ω ∂P₁ = 0)
    (hξsq : ∫ ω, ‖ξ₀ ω‖ ^ 2 ∂P₀ = s)
    (hξp : ∀ k : ℕ, MemLp ξ₀ (2 * k : ℕ) P₀) (hηp : ∀ k : ℕ, MemLp η₀ (2 * k : ℕ) P₁)
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, f x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, f x ∂semicircleReal 0 s|}) atTop (𝓝 0) :=
  tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability hindep
    (fun n ij hij ↦ (hξid n ij hij).integral_eq.trans hξzero)
    (fun n i hi ↦ (hηid n i hi).integral_eq.trans hηzero)
    (fun n ij hij ↦ (hξid n ij hij).norm.sq.integral_eq.trans hξsq)
    (fun k n ij hij ↦ (hξid n ij hij).memLp_iff.mpr (hξp k))
    (fun k n i hi ↦ (hηid n i hi).memLp_iff.mpr (hηp k))
    (fun _ ↦ ⟨_, fun n ij hij ↦ (hξid n ij hij).norm.pow.integral_eq.le⟩)
    (fun _ ↦ ⟨_, fun n i hi ↦ (hηid n i hi).norm.pow.integral_eq.le⟩)
    f hε

end TauCeti.Probability
