/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.MeasureTheory.Integral.Bind
public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.Moments.WeakConvergence
public import TauCeti.Probability.RandomMatrix.LeadingMoments

/-!
# Expected empirical spectral moments and expected semicircle law for Wigner matrices

For a Hermitian Wigner matrix `H_{n+1}`, the `k`th moment `∫ x ^ k dL_{H_{n+1}}` of its empirical
spectral measure is the real part of the normalized trace `(n + 1)⁻¹ tr(H_{n+1} ^ k)`. Against `P`,
this transfers the quantitative trace bounds from `TauCeti.Probability.RandomMatrix.MomentBounds`
and `TauCeti.Probability.RandomMatrix.LeadingMoments` directly to expected empirical spectral
moments:

* even expected spectral moments `E[∫ x ^ (2 * m) dL_{H_{n+1}}]` lie within `O((n + 1)⁻¹)` of
  `s ^ m * catalan m = ∫ x ^ (2 * m) ∂semicircleReal 0 s`;
* odd expected spectral moments `E[∫ x ^ (2 * m + 1) dL_{H_{n+1}}]` have magnitude
  `O((n + 1) ^ (-1/2))`, matching `∫ x ^ (2 * m + 1) ∂semicircleReal 0 s = 0`.

Because these finite-`n` bounds depend on `n` only through `(n + 1)⁻¹` and `(√(n + 1))⁻¹`,
expected spectral moment convergence of every order `k : ℕ` holds uniformly for triangular arrays on
varying probability spaces `(Ω n, P n)` without assuming identically distributed entries. When all
entry moments are uniformly bounded at each order, the mixture `(P n).bind L_{H_{n+1}}` — the
expected empirical spectral measure — has finite moments of every order and converges weakly to
`semicircleReal 0 s` by the method of moments
(`ProbabilityMeasure.tendsto_of_tendsto_integral_pow`).

## Main results

* `TauCeti.Probability.integral_pow_spectralMeasure_wignerMatrix`,
  `TauCeti.Probability.integral_integral_pow_spectralMeasure_wignerMatrix`, and
  `TauCeti.Probability.integral_pow_bind_spectralMeasure_wignerMatrix`: deterministic, expected, and
  mixture spectral moments expressed through normalized traces under `Lᵏ` corner entries.
* `TauCeti.Probability.abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le` and
  `TauCeti.Probability.abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le`:
  quantitative `O((n + 1)⁻¹)` and `O((√(n + 1))⁻¹)` error bounds against `semicircleReal 0 s`.
* `TauCeti.Probability.tendsto_integral_integral_pow_spectralMeasure_wignerMatrix_of_array` and
  `TauCeti.Probability.tendsto_integral_integral_pow_spectralMeasure_wignerMatrix`: convergence of
  expected empirical spectral moments of every order `k : ℕ` to `semicircleReal 0 s`.
* `TauCeti.Probability.tendsto_bind_spectralMeasure_wignerMatrix_of_array` and
  `TauCeti.Probability.tendsto_bind_spectralMeasure_wignerMatrix`: weak convergence of the expected
  empirical spectral measure to `semicircleReal 0 s`, together with bounded-continuous test-function
  corollaries.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace TauCeti.Probability

section FixedSpace

variable {Ω : Type*} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- The `k`th empirical spectral moment of the `(n + 1) × (n + 1)` Wigner matrix is the real part
of its normalized `k`th trace. -/
theorem integral_pow_spectralMeasure_wignerMatrix (n k : ℕ) (ω : Ω) :
    (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      (((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace).re := by
  rw [Matrix.integral_pow_spectralMeasure]
  simp only [Fintype.card_fin, RCLike.re_to_complex]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- On a finite measure space, the `k`th empirical spectral moment of the `(n + 1) × (n + 1)`
Wigner matrix is integrable whenever all coordinates in the `(n + 1) × (n + 1)` corner lie in
`Lᵏ`. -/
theorem integrable_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n + 1 → MemLp (ξ ij) k P)
    (hη : ∀ i < n + 1, MemLp (η i) k P) :
    Integrable (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P := by
  simp_rw [integral_pow_spectralMeasure_wignerMatrix]
  exact Complex.reCLM.integrable_comp
    ((integrable_trace_pow_wignerMatrix hξ hη).const_mul _)

/-- On a finite measure space with `Lᵏ` corner entries, the expected `k`th empirical spectral
moment is the real part of the normalized expected `k`th trace. -/
theorem integral_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n + 1 → MemLp (ξ ij) k P)
    (hη : ∀ i < n + 1, MemLp (η i) k P) :
    ∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P =
      (((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ k).trace ∂P).re := by
  simp_rw [integral_pow_spectralMeasure_wignerMatrix]
  rw [← integral_const_mul]
  simpa only [Complex.reCLM_apply] using
    Complex.reCLM.integral_comp_comm
      ((integrable_trace_pow_wignerMatrix hξ hη).const_mul _)

/-- **Quantitative expected even spectral moment bound.** For independent centered entries in the
`(n + 1) × (n + 1)` corner with `2m`th absolute moments bounded by `B` and strictly upper second
absolute moment `s`, the expected `2m`th empirical spectral moment of `H_{n+1}` lies within
`O((n + 1)⁻¹)` of the `2m`th moment of `semicircleReal 0 s` (for every `m n : ℕ`). -/
theorem abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le
    {m n : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.1.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.1) (fun i ω ↦ (η i.1 ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n + 1, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B)
    (hξsq : ∀ ij : StrictUpper, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    |(∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) -
      ∫ x, x ^ (2 * m) ∂semicircleReal 0 s| ≤
      ((m : ℝ) ^ (2 * m) * B + (s : ℝ) ^ m * catalan m * (m + 1).choose 2) / (n + 1 : ℕ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [integral_integral_pow_spectralMeasure_wignerMatrix hξp hηp,
    integral_pow_two_mul_semicircleReal_zero]
  calc |(((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ (2 * m)).trace ∂P).re -
          (s : ℝ) ^ m * catalan m|
      = |(((n + 1 : ℕ) : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η (n + 1) ω ^ (2 * m)).trace ∂P) -
          ((s : ℝ) : ℂ) ^ m * catalan m).re| := by
        congr 1
        have hre : (((s : ℝ) : ℂ) ^ m * catalan m).re = (s : ℝ) ^ m * catalan m := by norm_cast
        rw [Complex.sub_re, hre]
    _ ≤ ‖((n + 1 : ℕ) : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η (n + 1) ω ^ (2 * m)).trace ∂P) -
          ((s : ℝ) : ℂ) ^ m * catalan m‖ := Complex.abs_re_le_norm _
    _ ≤ ((m : ℝ) ^ (2 * m) * B + (s : ℝ) ^ m * catalan m * (m + 1).choose 2) / (n + 1 : ℕ) :=
        norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_le
          (Nat.add_one_ne_zero n) s.coe_nonneg hindep hξzero hηzero hξp hηp hξ hη hξsq

/-- **Quantitative expected odd spectral moment bound.** For independent centered entries in the
`(n + 1) × (n + 1)` corner with `(2m + 1)`st absolute moments bounded by `B`, the expected
`(2m + 1)`st empirical spectral moment of `H_{n+1}` has magnitude at most
`(m + 1) ^ (2 * m + 1) * B / √(n + 1)`. -/
theorem abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
    {m n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.1.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.1) (fun i ω ↦ (η i.1 ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.1.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n + 1, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.1.2 < n + 1 → MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hB : 0 ≤ B := (integral_nonneg fun _ ↦ by positivity).trans (hη 0 (Nat.zero_lt_succ n))
  rw [integral_integral_pow_spectralMeasure_wignerMatrix hξp hηp]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hodd := norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le (n := n + 1)
    (ξ := fun ij ↦ if ij.1.2 < n + 1 then ξ ij else 0)
    (η := fun i ↦ if i < n + 1 then η i else 0)
    (iIndepFun_sumElim_ofReal_ite_lt hindep)
    (fun ij ↦ by by_cases h : ij.1.2 < n + 1 <;> simp [h, hξzero])
    (fun i ↦ by by_cases h : i < n + 1 <;> simp [h, hηzero])
    (fun ij ↦ by
      by_cases h : ij.1.2 < n + 1
      · simpa [h] using hξp ij h
      · simp [h, MemLp.zero])
    (fun i ↦ by
      by_cases h : i < n + 1
      · simpa [h] using hηp i h
      · simp [h, MemLp.zero])
    (fun ij ↦ by
      by_cases h : ij.1.2 < n + 1
      · simpa [h] using hξ ij h
      · simpa [h, zero_pow (Nat.add_one_ne_zero (2 * m))] using hB)
    (fun i ↦ by
      by_cases h : i < n + 1
      · simpa [h] using hη i h
      · simpa [h, zero_pow (Nat.add_one_ne_zero (2 * m))] using hB)
  simpa only [wignerMatrix_ite_lt] using hodd

/-- The empirical spectral measure of the `(n + 1) × (n + 1)` Wigner matrix, viewed as a random
measure on `ℝ`, is almost everywhere measurable whenever the corner entry coordinates are. -/
theorem aemeasurable_spectralMeasure_wignerMatrix {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, AEMeasurable (η i) P) :
    AEMeasurable (fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P := by
  have hW : AEMeasurable (wignerMatrix ξ η (n + 1)) P :=
    (aemeasurable_wignerMatrix
      (ξ := fun ij ↦ if ij.1.2 < n + 1 then ξ ij else 0)
      (η := fun i ↦ if i < n + 1 then η i else 0)
      (fun ij ↦ by
        by_cases h : ij.1.2 < n + 1
        · simpa [h] using hξ ij h
        · rw [ite_eq_right_iff.mpr fun h' ↦ (h h').elim]; exact aemeasurable_const)
      (fun i ↦ by
        by_cases h : i < n + 1
        · simpa [h] using hη i h
        · rw [ite_eq_right_iff.mpr fun h' ↦ (h h').elim]; exact aemeasurable_const)
      (n + 1)).congr (.of_forall fun ω ↦ wignerMatrix_ite_lt ξ η (n + 1) ω)
  have hH : AEMeasurable (Set.codRestrict (wignerMatrix ξ η (n + 1)) {A | A.IsHermitian}
      fun ω ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) P :=
    hW.subtype_mk
  exact (measurable_subtype_coe.comp Matrix.measurable_spectralMeasure).comp_aemeasurable hH

/-- On a probability space, the mixture `P.bind L_{H_{n+1}}` — the expected empirical spectral
measure of the Wigner matrix — is a probability measure whenever the corner entry coordinates are
almost everywhere measurable. -/
theorem isProbabilityMeasure_bind_spectralMeasure_wignerMatrix [IsProbabilityMeasure P] {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, AEMeasurable (η i) P) :
    IsProbabilityMeasure (P.bind fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) :=
  isProbabilityMeasure_bind (aemeasurable_spectralMeasure_wignerMatrix hξ hη)
    (.of_forall fun _ ↦ inferInstance)

/-- On a finite measure space, the monomial `x ↦ x ^ k` is integrable against the expected
empirical spectral measure `P.bind L_{H_{n+1}}` whenever the corner entry coordinates lie in
`Lᵏ`. -/
theorem integrable_pow_bind_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k n : ℕ}
    (hξp : ∀ ij : StrictUpper, ij.1.2 < n + 1 → MemLp (ξ ij) (k : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (k : ℕ) P) :
    Integrable (fun x : ℝ ↦ x ^ k)
      (P.bind fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) := by
  set L : Ω → Measure ℝ := fun ω ↦
    ((wignerMatrix ξ η (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian ξ η ω (n + 1)) :
      Measure ℝ)
  have hL : AEMeasurable L P := aemeasurable_spectralMeasure_wignerMatrix
    (fun ij hij ↦ (hξp ij hij).aestronglyMeasurable.aemeasurable)
    (fun i hi ↦ (hηp i hi).aestronglyMeasurable.aemeasurable)
  refine ⟨(continuous_pow k).aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
  rw [Measure.lintegral_bind hL (by fun_prop)]
  let S : Ω → ℝ := fun ω ↦
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ‖wignerMatrix ξ η (n + 1) ω i j‖
  let M : Ω → ℝ := fun ω ↦ ((n + 1 : ℕ) : ℝ) * S ω
  have hHij (i j : Fin (n + 1)) : MemLp (fun ω ↦ wignerMatrix ξ η (n + 1) ω i j) (k : ℕ) P := by
    have h := memLp_wignerMatrix_apply (p := (k : ℕ))
      (ξ := fun ij ↦ if ij.1.2 < n + 1 then ξ ij else 0)
      (η := fun i ↦ if i < n + 1 then η i else 0)
      (fun ij ↦ by
        by_cases h : ij.1.2 < n + 1
        · simpa [h] using hξp ij h
        · simp [h, MemLp.zero])
      (fun i ↦ by
        by_cases h : i < n + 1
        · simpa [h] using hηp i h
        · simp [h, MemLp.zero])
      i j
    simpa only [wignerMatrix_ite_lt] using h
  have hM : MemLp M (k : ℕ) P :=
    (memLp_finsetSum Finset.univ fun i _ ↦
      memLp_finsetSum Finset.univ fun j _ ↦ (hHij i j).norm).const_mul _
  have hMint : Integrable (fun ω ↦ ‖M ω‖ ^ k) P := hM.integrable_norm_pow'
  have hcomp (ω : Ω) : ∫⁻ x, ENNReal.ofReal ‖x ^ k‖ ∂L ω ≤ ENNReal.ofReal (‖M ω‖ ^ k) := by
    have hint_pow : Integrable (fun x : ℝ ↦ ‖x ^ k‖) (L ω) := by
      dsimp only [L]
      rw [Matrix.spectralMeasure_def, empiricalMeasureOfFintype_toMeasure]
      exact integrable_finsetSum_measure.mpr fun _ _ ↦
        (integrable_dirac (by simp)).smul_measure (ENNReal.inv_ne_top.mpr (by simp))
    rw [← ofReal_integral_eq_lintegral_ofReal hint_pow (.of_forall fun _ ↦ norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = ((n + 1 : ℕ) : ℝ) := by simp
    rw [Matrix.integral_spectralMeasure_eq_sum_eigenvalues₀, smul_eq_mul, hcard]
    have hentry (i j : Fin (n + 1)) : ‖wignerMatrix ξ η (n + 1) ω i j‖ ≤ S ω :=
      (Finset.single_le_sum (fun j' _ ↦ norm_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum
          (fun i' _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i))
    have heig (r : Fin (Fintype.card (Fin (n + 1)))) :
        ‖(wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ r ^ k‖ ≤ ‖M ω‖ ^ k := by
      have habs : |(wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ r| ≤ M ω := by
        simpa only [Fintype.card_fin, M] using
          (wignerMatrix_isHermitian ξ η ω (n + 1)).abs_eigenvalues₀_le_of_entry_le hentry r
      rw [norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (habs.trans (le_abs_self _)) k
    have hsum : ∑ r : Fin (Fintype.card (Fin (n + 1))),
        ‖(wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ r ^ k‖ ≤
        ((n + 1 : ℕ) : ℝ) * ‖M ω‖ ^ k := by
      calc ∑ r : Fin (Fintype.card (Fin (n + 1))),
              ‖(wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ r ^ k‖
          ≤ ∑ _r : Fin (Fintype.card (Fin (n + 1))), ‖M ω‖ ^ k :=
            Finset.sum_le_sum fun r _ ↦ heig r
        _ = ((n + 1 : ℕ) : ℝ) * ‖M ω‖ ^ k := by
            simp [Fintype.card_fin]
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.add_one_ne_zero n)
    calc (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ r : Fin (Fintype.card (Fin (n + 1))),
            ‖(wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ r ^ k‖)
        ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ) * ‖M ω‖ ^ k) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ‖M ω‖ ^ k := inv_mul_cancel_left₀ hn1 _
  calc ∫⁻ ω, ∫⁻ x, ENNReal.ofReal ‖x ^ k‖ ∂L ω ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (‖M ω‖ ^ k) ∂P := lintegral_mono hcomp
    _ = ENNReal.ofReal (∫ ω, ‖M ω‖ ^ k ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hMint (.of_forall fun _ ↦ by positivity)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- On a finite measure space with `Lᵏ` corner entries, the `k`th moment of the expected empirical
spectral measure `P.bind L_{H_{n+1}}` equals the expected `k`th empirical spectral moment. -/
theorem integral_pow_bind_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k n : ℕ}
    (hξp : ∀ ij : StrictUpper, ij.1.2 < n + 1 → MemLp (ξ ij) (k : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (k : ℕ) P) :
    (∫ x, x ^ k ∂(P.bind fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))) =
      ∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P :=
  Measure.integral_bind
    (aemeasurable_spectralMeasure_wignerMatrix
      (fun ij hij ↦ (hξp ij hij).aestronglyMeasurable.aemeasurable)
      (fun i hi ↦ (hηp i hi).aestronglyMeasurable.aemeasurable))
    (integrable_pow_bind_spectralMeasure_wignerMatrix hξp hηp)

end FixedSpace

section Convergence

/-- **Expected spectral moment convergence for triangular Wigner arrays.** For independent centered
entries in the `(n + 1) × (n + 1)` corner on possibly varying probability spaces `(Ω n, P n)`
whose `k`th absolute moments are uniformly bounded by `B` and whose strictly upper entries have
common second absolute moment `s`, the expected `k`th empirical spectral moment of `H_{n+1}`
converges to the `k`th moment of `semicircleReal 0 s` (for every `k : ℕ`). -/
theorem tendsto_integral_integral_pow_spectralMeasure_wignerMatrix_of_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.1.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.1) (fun i ω ↦ (η n i.1 ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k
        ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 s)) := by
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  rcases k.even_or_odd' with ⟨m, rfl | rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        ((m : ℝ) ^ (2 * m) * B + (s : ℝ) ^ m * catalan m * (m + 1).choose 2) /
          (n + 1 : ℕ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop hnat
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hlim
    rw [Real.norm_eq_abs]
    exact abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) (hξsq n)
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hnat)
    refine squeeze_zero_norm (fun n ↦ ?_) hlim
    rw [Real.norm_eq_abs]
    exact abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n)

/-- **Expected spectral moment convergence for Wigner matrices.** On a single infinite entry array
with independent centered coordinates, uniformly bounded `k`th absolute moments, and common
off-diagonal second absolute moment `s`, the expected `k`th empirical spectral moment of `H_{n+1}`
converges to `∫ x ^ k ∂semicircleReal 0 s` (for every `k : ℕ`). -/
theorem tendsto_integral_integral_pow_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (k : ℕ) P) (hηp : ∀ i, MemLp (η i) (k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k
        ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 s)) :=
  tendsto_integral_integral_pow_spectralMeasure_wignerMatrix_of_array
    (fun _ ↦ (iIndepFun.precomp
        (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩) hindep).congr
      fun r ↦ .of_forall fun _ ↦ by rcases r with ij | i <;> rfl)
    (fun _ ij _ ↦ hξzero ij) (fun _ i _ ↦ hηzero i)
    (fun _ ij _ ↦ hξp ij) (fun _ i _ ↦ hηp i)
    (fun _ ij _ ↦ hξ ij) (fun _ i _ ↦ hη i) (fun _ ij _ ↦ hξsq ij)

/-- **Weak convergence of expected empirical spectral measures for triangular Wigner arrays.**
For independent centered corner entries on varying spaces `(Ω n, P n)` with common off-diagonal
second absolute moment `s` and uniformly bounded moments of every order, the expected empirical
spectral measures `(P n).bind L_{H_{n+1}}` converge weakly to `semicircleReal 0 s`. -/
theorem tendsto_bind_spectralMeasure_wignerMatrix_of_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.1.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.1) (fun i ω ↦ (η n i.1 ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ k n (ij : StrictUpper), ij.1.2 < n + 1 → MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ k n, ∀ i < n + 1, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ ⟨(P n).bind fun ω ↦ ((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ),
        have := (hindep n).isProbabilityMeasure
        isProbabilityMeasure_bind_spectralMeasure_wignerMatrix
          (fun ij hij ↦ (hξp 0 n ij hij).aestronglyMeasurable.aemeasurable)
          (fun i hi ↦ (hηp 0 n i hi).aestronglyMeasurable.aemeasurable)⟩)
      atTop (𝓝 ⟨semicircleReal 0 s, inferInstance⟩) := by
  have hprob (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  refine ProbabilityMeasure.tendsto_of_tendsto_integral_pow
    (K := Set.Icc (0 - 2 * Real.sqrt s) (0 + 2 * Real.sqrt s)) isCompact_Icc
    (ae_iff.mp (ae_mem_Icc_semicircleReal 0 s))
    (fun k ↦ Eventually.of_forall fun n ↦
      integrable_pow_bind_spectralMeasure_wignerMatrix (hξp k n) (hηp k n))
    fun k ↦ ?_
  obtain ⟨B₁, hB₁⟩ := hξ k
  obtain ⟨B₂, hB₂⟩ := hη k
  have hconv := tendsto_integral_integral_pow_spectralMeasure_wignerMatrix_of_array
    (B := max B₁ B₂) hindep hξzero hηzero (hξp k) (hηp k)
    (fun n ij hij ↦ (hB₁ n ij hij).trans (le_max_left _ _))
    (fun n i hi ↦ (hB₂ n i hi).trans (le_max_right _ _)) hξsq
  exact hconv.congr fun n ↦
    (integral_pow_bind_spectralMeasure_wignerMatrix (hξp k n) (hηp k n)).symm

/-- **Weak convergence of the expected empirical spectral measure for Wigner matrices.**
On a single infinite entry array with independent centered coordinates, common off-diagonal second
absolute moment `s`, and uniformly bounded moments of every order, `P.bind L_{H_{n+1}}` converges
weakly to `semicircleReal 0 s`. -/
theorem tendsto_bind_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ k ij, MemLp (ξ ij) (k : ℕ) P) (hηp : ∀ k i, MemLp (η i) (k : ℕ) P)
    (hξ : ∀ k, ∃ B, ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B)
    (hη : ∀ k, ∃ B, ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ ⟨P.bind fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ),
        have := hindep.isProbabilityMeasure
        isProbabilityMeasure_bind_spectralMeasure_wignerMatrix
          (fun ij _ ↦ (hξp 0 ij).aestronglyMeasurable.aemeasurable)
          (fun i _ ↦ (hηp 0 i).aestronglyMeasurable.aemeasurable)⟩)
      atTop (𝓝 ⟨semicircleReal 0 s, inferInstance⟩) :=
  tendsto_bind_spectralMeasure_wignerMatrix_of_array
    (fun _ ↦ (iIndepFun.precomp
        (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩) hindep).congr
      fun r ↦ .of_forall fun _ ↦ by rcases r with ij | i <;> rfl)
    (fun _ ij _ ↦ hξzero ij) (fun _ i _ ↦ hηzero i)
    (fun k _ ij _ ↦ hξp k ij) (fun k _ i _ ↦ hηp k i)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ij _ ↦ hB ij⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ i _ ↦ hB i⟩)
    (fun _ ij _ ↦ hξsq ij)

/-- For any bounded continuous test function `f : ℝ →ᵇ ℝ` and triangular Wigner array satisfying
the corner moment hypotheses, `E[∫ f dL_{H_{n+1}}]` converges to `∫ f ∂semicircleReal 0 s`. -/
theorem tendsto_integral_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix_of_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.1.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.1) (fun i ω ↦ (η n i.1 ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n, ∀ i < n + 1, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ k n (ij : StrictUpper), ij.1.2 < n + 1 → MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ k n, ∀ i < n + 1, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n (ij : StrictUpper), ij.1.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s)
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, f x
        ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, f x ∂semicircleReal 0 s)) := by
  have hweak := tendsto_bind_spectralMeasure_wignerMatrix_of_array
    hindep hξzero hηzero hξp hηp hξ hη hξsq
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) f
  refine hf.congr fun n ↦ ?_
  have : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hL := aemeasurable_spectralMeasure_wignerMatrix
    (fun ij hij ↦ (hξp 0 n ij hij).aestronglyMeasurable.aemeasurable)
    (fun i hi ↦ (hηp 0 n i hi).aestronglyMeasurable.aemeasurable)
  have : IsProbabilityMeasure ((P n).bind fun ω ↦
      ((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) :=
    isProbabilityMeasure_bind_spectralMeasure_wignerMatrix
      (fun ij hij ↦ (hξp 0 n ij hij).aestronglyMeasurable.aemeasurable)
      (fun i hi ↦ (hηp 0 n i hi).aestronglyMeasurable.aemeasurable)
  exact Measure.integral_bind hL (f.integrable _)

/-- For any bounded continuous test function `f : ℝ →ᵇ ℝ` on a single infinite Wigner array
satisfying the moment hypotheses, `E[∫ f dL_{H_{n+1}}]` converges to `∫ f ∂semicircleReal 0 s`. -/
theorem tendsto_integral_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ k ij, MemLp (ξ ij) (k : ℕ) P) (hηp : ∀ k i, MemLp (η i) (k : ℕ) P)
    (hξ : ∀ k, ∃ B, ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B)
    (hη : ∀ k, ∃ B, ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, f x
        ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 (∫ x, f x ∂semicircleReal 0 s)) :=
  tendsto_integral_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix_of_array
    (fun _ ↦ (iIndepFun.precomp
        (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩) hindep).congr
      fun r ↦ .of_forall fun _ ↦ by rcases r with ij | i <;> rfl)
    (fun _ ij _ ↦ hξzero ij) (fun _ i _ ↦ hηzero i)
    (fun k _ ij _ ↦ hξp k ij) (fun k _ i _ ↦ hηp k i)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ij _ ↦ hB ij⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ i _ ↦ hB i⟩)
    (fun _ ij _ ↦ hξsq ij) f

end Convergence

end TauCeti.Probability
