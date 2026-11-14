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

Combining the moment-method spectral-moment convergence from
`TauCeti.Probability.RandomMatrix.SpectralMoment.Moments` with the compact-support method of
moments (`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow` and
`MeasureTheory.ProbabilityMeasure.tendsto_measure_abs_integral_sub_ge_of_isCompact`), this file
proves Wigner's semicircle law for `(n + 1) × (n + 1)` Hermitian Wigner matrices whose corner
entries are independent and centered at each matrix size, have unit off-diagonal second absolute
moments, and have uniformly bounded even moments of every order:

1. **Almost-sure weak convergence.** For any sequence of Wigner arrays `(ξ n, η n)` on `(Ω, P)`
   whose `(n + 1) × (n + 1)` corner entries satisfy these conditions at each matrix size `n` (with
   no independence assumption across different `n`), the empirical spectral measure of
   `wignerMatrix (ξ n) (η n) (n + 1)` converges weakly almost surely in `ProbabilityMeasure ℝ` to
   `⟨semicircleReal 0 1, inferInstance⟩`. We specialize this to the principal corners of a single
   infinite Wigner array and to arrays whose strictly-upper-triangular and diagonal entries are
   identically distributed with reference random variables possessing finite moments of all even
   orders.
2. **Weak convergence in probability.** On possibly varying sample spaces `(Ω n, P n)`, for every
   bounded continuous function `f : ℝ →ᵇ ℝ` and every `ε > 0`, the probability that
   `|∫ x, f x dL_{H_{n+1}} - ∫ x, f x d(semicircleReal 0 1)| ≥ ε` tends to `0` as `n → ∞`.

## Main results

In the `TauCeti.Probability` namespace:

* `ae_tendsto_spectralMeasure_wignerMatrix_of_seq` — almost-sure weak convergence of empirical
  spectral measures for a sequence of Wigner arrays with uniformly bounded even moments on each
  `(n + 1) × (n + 1)` corner.
* `ae_tendsto_spectralMeasure_wignerMatrix` — almost-sure weak convergence for the corners of a
  single infinite Wigner array with uniformly bounded even moments.
* `ae_tendsto_spectralMeasure_wignerMatrix_of_identDistrib` — almost-sure weak convergence when the
  off-diagonal and diagonal entries are identically distributed with reference variables having
  finite even moments of all orders.
* `tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability` — convergence in
  probability of bounded continuous linear statistics on possibly varying probability spaces.
* `tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability_of_identDistrib` —
  in-probability convergence when the corner entries at each matrix size are identically
  distributed with fixed reference variables.

## References

* E. P. Wigner, *Characteristic vectors of bordered matrices with infinite dimensions*,
  Ann. of Math. (2) **62** (1955), 548–564.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.1–§2.1.3, Theorem 2.1.1 (bounded-moments semicircle law proved
  via Lemmas 2.1.6 and 2.1.7).
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012), §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.Probability

private theorem semicircleReal_compl_Icc_eq_zero :
    (semicircleReal 0 1)
      (Set.Icc ((0 : ℝ) - 2 * Real.sqrt (1 : ℝ≥0)) ((0 : ℝ) + 2 * Real.sqrt (1 : ℝ≥0)))ᶜ = 0 :=
  ae_iff.mp (ae_mem_Icc_semicircleReal 0 1)

/-- **Wigner's semicircle law (almost surely, sequence of arrays).** For any sequence of Wigner
arrays `(ξ n, η n)` on `(Ω, P)` whose `(n + 1) × (n + 1)` corner entries at each matrix size `n`
are independent and centered with unit off-diagonal second absolute moments, and whose even
absolute moments of each order `2 * k` are uniformly bounded across `n` and the corner indices, the
empirical spectral measure of `wignerMatrix (ξ n) (η n) (n + 1)` converges weakly almost surely to
`semicircleReal 0 1`. No independence across different matrix sizes `n` is required. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_of_seq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) P)
    (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P = 0)
    (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P = 0)
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ k n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ k n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ k, ∃ B, ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ k, ∃ B, ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 1, inferInstance⟩) := by
  have hae (k : ℕ) : ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
    obtain ⟨B₁, hB₁⟩ := hξ k
    obtain ⟨B₂, hB₂⟩ := hη k
    exact ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
      hindep hξzero hηzero hsecond (hξp k) (hηp k)
      (fun n ij hij ↦ (hB₁ n ij hij).trans (le_max_left B₁ B₂))
      (fun n i hi ↦ (hB₂ n i hi).trans (le_max_right B₁ B₂))
  filter_upwards [ae_all_iff.2 hae] with ω hω
  exact ProbabilityMeasure.tendsto_of_tendsto_integral_pow
    isCompact_Icc semicircleReal_compl_Icc_eq_zero
    (fun k ↦ Eventually.of_forall fun n ↦ Matrix.integrable_pow_spectralMeasure _ _ k)
    hω

/-- **Wigner's semicircle law (almost surely, infinite array).** For an infinite Wigner array
`(ξ, η)` on `(Ω, P)` with independent centered entries, unit off-diagonal second absolute moments,
and uniformly bounded even moments of every order, the empirical spectral measure of
`wignerMatrix ξ η (n + 1)` converges weakly almost surely to `semicircleReal 0 1`. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ k ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ k i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ k, ∃ B, ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ k, ∃ B, ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 1, inferInstance⟩) :=
  ae_tendsto_spectralMeasure_wignerMatrix_of_seq
    (fun n ↦ hindep.precomp (wignerCoordinateIndex_injective (n + 1)))
    (fun _ ij _ ↦ hξzero ij) (fun _ i _ ↦ hηzero i) (fun _ ij _ ↦ hsecond ij)
    (fun k _ ij _ ↦ hξp k ij) (fun k _ i _ ↦ hηp k i)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ij _ ↦ hB ij⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ i _ ↦ hB i⟩)

/-- **Wigner's semicircle law (almost surely, identically distributed entries).** When the
upper-triangular entries `ξ ij` are identically distributed with a centered unit-variance complex
random variable `ξ₀` having finite even moments of all orders and the diagonal entries `η i` are
identically distributed with a centered real random variable `η₀` having finite even moments of all
orders, and all upper-triangular and diagonal entries are mutually independent, the empirical
spectral measure of `wignerMatrix ξ η (n + 1)` converges weakly almost surely to
`semicircleReal 0 1`. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_of_identDistrib
    {Ω Ω₀ Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    {P : Measure Ω} {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}
    {ξ₀ : Ω₀ → ℂ} {η₀ : Ω₁ → ℝ}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξid : ∀ ij, IdentDistrib (ξ ij) ξ₀ P P₀)
    (hηid : ∀ i, IdentDistrib (η i) η₀ P P₁)
    (hξzero : ∫ ω, ξ₀ ω ∂P₀ = 0)
    (hηzero : ∫ ω, η₀ ω ∂P₁ = 0)
    (hsecond : ∫ ω, ‖ξ₀ ω‖ ^ 2 ∂P₀ = 1)
    (hξp : ∀ k : ℕ, MemLp ξ₀ (2 * k : ℕ) P₀)
    (hηp : ∀ k : ℕ, MemLp η₀ (2 * k : ℕ) P₁) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 1, inferInstance⟩) :=
  ae_tendsto_spectralMeasure_wignerMatrix hindep
    (fun ij ↦ (hξid ij).integral_eq.trans hξzero)
    (fun i ↦ (hηid i).integral_eq.trans hηzero)
    (fun ij ↦ ((hξid ij).comp (by fun_prop : Measurable fun z : ℂ ↦ ‖z‖ ^ 2)).integral_eq.trans
      hsecond)
    (fun k ij ↦ (hξid ij).memLp_iff.mpr (hξp k))
    (fun k i ↦ (hηid i).memLp_iff.mpr (hηp k))
    (fun k ↦ ⟨∫ ω, ‖ξ₀ ω‖ ^ (2 * k) ∂P₀, fun ij ↦
      ((hξid ij).comp (by fun_prop : Measurable fun z : ℂ ↦ ‖z‖ ^ (2 * k))).integral_eq.le⟩)
    (fun k ↦ ⟨∫ ω, ‖η₀ ω‖ ^ (2 * k) ∂P₁, fun i ↦
      ((hηid i).comp (by fun_prop : Measurable fun x : ℝ ↦ ‖x‖ ^ (2 * k))).integral_eq.le⟩)

/-- **Wigner's semicircle law (in probability).** On possibly varying probability spaces
`(Ω n, P n)`, if for each `n` the `(n + 1) × (n + 1)` corner entries of `(ξ n, η n)` are
independent and centered with unit off-diagonal second absolute moments, and for every `k` the
`2 * k`th absolute moments are uniformly bounded across `n` and the corner indices, then for every
bounded continuous function `f : ℝ →ᵇ ℝ` and every `ε > 0`,
`P n {ω | ε ≤ |∫ f dL_{H_{n+1}(ω)} - ∫ f d(semicircleReal 0 1)|} → 0` as `n → ∞`. -/
theorem tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) (P n))
    (hξzero : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, i < n + 1 → ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ k n ij, ij.1.2 < n + 1 → MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ k n i, i < n + 1 → MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n ij, ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n i, i < n + 1 → ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, f x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, f x ∂semicircleReal 0 1|}) atTop (𝓝 0) := by
  refine ProbabilityMeasure.tendsto_measure_abs_integral_sub_ge_of_isCompact
    (ν := fun n ω ↦ (wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)))
    (μ := ⟨semicircleReal 0 1, inferInstance⟩)
    isCompact_Icc semicircleReal_compl_Icc_eq_zero
    (Eventually.of_forall fun n ↦ .of_forall fun ω k ↦
      Matrix.integrable_pow_spectralMeasure _ _ k)
    (fun k {η_tol} hη_pos ↦ ?_) f hε
  obtain ⟨B₁, hB₁⟩ := hξ k
  obtain ⟨B₂, hB₂⟩ := hη k
  exact tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_semicircleReal_probability
    hindep hξzero hηzero hsecond (hξp k) (hηp k)
    (fun n ij hij ↦ (hB₁ n ij hij).trans (le_max_left B₁ B₂))
    (fun n i hi ↦ (hB₂ n i hi).trans (le_max_right B₁ B₂))
    hη_pos

/-- **Wigner's semicircle law (in probability, identically distributed entries).** Specialization of
`tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability` when for each
matrix size `n` the `(n + 1) × (n + 1)` corner entries `ξ n ij` and `η n i` are identically
distributed with reference variables `ξ₀` and `η₀` possessing finite even moments of all orders. -/
theorem tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability_of_identDistrib
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {Ω₀ Ω₁ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {ξ₀ : Ω₀ → ℂ} {η₀ : Ω₁ → ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ))
        (wignerCoordinateIndex (n + 1) r)) (P n))
    (hξid : ∀ n ij, ij.1.2 < n + 1 → IdentDistrib (ξ n ij) ξ₀ (P n) P₀)
    (hηid : ∀ n i, i < n + 1 → IdentDistrib (η n i) η₀ (P n) P₁)
    (hξzero : ∫ ω, ξ₀ ω ∂P₀ = 0)
    (hηzero : ∫ ω, η₀ ω ∂P₁ = 0)
    (hsecond : ∫ ω, ‖ξ₀ ω‖ ^ 2 ∂P₀ = 1)
    (hξp : ∀ k : ℕ, MemLp ξ₀ (2 * k : ℕ) P₀)
    (hηp : ∀ k : ℕ, MemLp η₀ (2 * k : ℕ) P₁)
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, f x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, f x ∂semicircleReal 0 1|}) atTop (𝓝 0) :=
  tendsto_integral_spectralMeasure_wignerMatrix_sub_semicircleReal_probability hindep
    (fun n ij hij ↦ (hξid n ij hij).integral_eq.trans hξzero)
    (fun n i hi ↦ (hηid n i hi).integral_eq.trans hηzero)
    (fun n ij hij ↦ ((hξid n ij hij).comp
      (by fun_prop : Measurable fun z : ℂ ↦ ‖z‖ ^ 2)).integral_eq.trans hsecond)
    (fun k n ij hij ↦ (hξid n ij hij).memLp_iff.mpr (hξp k))
    (fun k n i hi ↦ (hηid n i hi).memLp_iff.mpr (hηp k))
    (fun k ↦ ⟨∫ ω, ‖ξ₀ ω‖ ^ (2 * k) ∂P₀, fun n ij hij ↦
      ((hξid n ij hij).comp (by fun_prop : Measurable fun z : ℂ ↦ ‖z‖ ^ (2 * k))).integral_eq.le⟩)
    (fun k ↦ ⟨∫ ω, ‖η₀ ω‖ ^ (2 * k) ∂P₁, fun n i hi ↦
      ((hηid n i hi).comp (by fun_prop : Measurable fun x : ℝ ↦ ‖x‖ ^ (2 * k))).integral_eq.le⟩)
    f hε

end TauCeti.Probability
