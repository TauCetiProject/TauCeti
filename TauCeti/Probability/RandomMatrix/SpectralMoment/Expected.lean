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

* `TauCeti.Probability.integral_pow_spectralMeasure_wignerMatrix` and
  `TauCeti.Probability.integral_integral_pow_spectralMeasure_wignerMatrix`: deterministic and
  expected spectral moments expressed through normalized traces.
* `TauCeti.Probability.abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le` and
  `TauCeti.Probability.abs_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le`:
  quantitative `O((n + 1)⁻¹)` and `O((√(n + 1))⁻¹)` error bounds against `semicircleReal 0 s`.
* `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix_of_array` and
  `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix`: convergence of expected
  empirical spectral moments of every order `k : ℕ` to `semicircleReal 0 s`.
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
Wigner matrix is integrable whenever all array coordinates lie in `Lᵏ`. -/
theorem integrable_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξ : ∀ ij, MemLp (ξ ij) k P) (hη : ∀ i, MemLp (η i) k P) (n : ℕ) :
    Integrable (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P := by
  simp_rw [integral_pow_spectralMeasure_wignerMatrix]
  exact Complex.reCLM.integrable_comp
    ((integrable_trace_pow_wignerMatrix hξ hη (n + 1)).const_mul _)

/-- On a finite measure space with `Lᵏ` entries, the expected `k`th empirical spectral moment is
the real part of the normalized expected `k`th trace. -/
theorem integral_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξ : ∀ ij, MemLp (ξ ij) k P) (hη : ∀ i, MemLp (η i) k P) (n : ℕ) :
    ∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P =
      (((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ k).trace ∂P).re := by
  simp_rw [integral_pow_spectralMeasure_wignerMatrix]
  rw [← integral_const_mul]
  simpa only [Complex.reCLM_apply] using
    Complex.reCLM.integral_comp_comm
      ((integrable_trace_pow_wignerMatrix hξ hη (n + 1)).const_mul _)

/-- **Quantitative expected even spectral moment bound.** For independent centered entries with
`2m`th absolute moments bounded by `B` and off-diagonal second absolute moment `s`, the expected
`2m`th empirical spectral moment of `H_{n+1}` lies within `O((n + 1)⁻¹)` of the `2m`th moment of
`semicircleReal 0 s` (for every `m n : ℕ`). -/
theorem abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le {m n : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
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
          (Nat.add_one_ne_zero n) hindep hξzero hηzero hξp hηp hξ hη hξsq

/-- **Quantitative expected odd spectral moment bound.** For independent centered entries with
`(2m + 1)`st absolute moments bounded by `B`, the expected `(2m + 1)`st empirical spectral moment
of `H_{n+1}` has magnitude at most `(m + 1) ^ (2 * m + 1) * B / √(n + 1)`. -/
theorem abs_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le {m n : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [integral_integral_pow_spectralMeasure_wignerMatrix hξp hηp]
  exact (Complex.abs_re_le_norm _).trans
    (norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le
      hindep hξzero hηzero hξp hηp hξ hη)

/-- The empirical spectral measure of the `(n + 1) × (n + 1)` Wigner matrix, viewed as a random
measure on `ℝ`, is almost everywhere measurable whenever the entry coordinates are. -/
theorem aemeasurable_spectralMeasure_wignerMatrix
    (hξ : ∀ ij, AEMeasurable (ξ ij) P) (hη : ∀ i, AEMeasurable (η i) P) (n : ℕ) :
    AEMeasurable (fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P := by
  have hH : AEMeasurable (Set.codRestrict (wignerMatrix ξ η (n + 1)) {A | A.IsHermitian}
      fun ω ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) P :=
    (aemeasurable_wignerMatrix hξ hη (n + 1)).subtype_mk
  exact (measurable_subtype_coe.comp Matrix.measurable_spectralMeasure).comp_aemeasurable hH

/-- On a probability space, the mixture `P.bind L_{H_{n+1}}` — the expected empirical spectral
measure of the Wigner matrix — is a probability measure whenever the entry coordinates are almost
everywhere measurable. -/
theorem isProbabilityMeasure_bind_spectralMeasure_wignerMatrix [IsProbabilityMeasure P]
    (hξ : ∀ ij, AEMeasurable (ξ ij) P) (hη : ∀ i, AEMeasurable (η i) P) (n : ℕ) :
    IsProbabilityMeasure (P.bind fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) :=
  isProbabilityMeasure_bind (aemeasurable_spectralMeasure_wignerMatrix hξ hη n)
    (.of_forall fun _ ↦ inferInstance)

/-- On a finite measure space, the monomial `x ↦ x ^ k` is integrable against the expected
empirical spectral measure `P.bind L_{H_{n+1}}` whenever the entry coordinates lie in
`L^(2 * k)`. -/
theorem integrable_pow_bind_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k)
      (P.bind fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) := by
  set L : Ω → Measure ℝ := fun ω ↦
    ((wignerMatrix ξ η (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian ξ η ω (n + 1)) :
      Measure ℝ)
  have hL : AEMeasurable L P := aemeasurable_spectralMeasure_wignerMatrix
    (fun ij ↦ (hξp ij).aestronglyMeasurable.aemeasurable)
    (fun i ↦ (hηp i).aestronglyMeasurable.aemeasurable) n
  refine ⟨(continuous_pow k).aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
  rw [Measure.lintegral_bind hL (by fun_prop)]
  have hdom_pt (x : ℝ) : ‖x ^ k‖ ≤ 1 + x ^ (2 * k) := by
    rw [Real.norm_eq_abs, mul_comm 2 k, pow_mul, ← sq_abs]
    nlinarith [sq_nonneg (|x ^ k| - 1), abs_nonneg (x ^ k)]
  have hcomp (ω : Ω) : ∫⁻ x, ENNReal.ofReal ‖x ^ k‖ ∂L ω ≤
      ENNReal.ofReal (1 + ∫ x, x ^ (2 * k) ∂L ω) := by
    have hint_pow : Integrable (fun x : ℝ ↦ x ^ (2 * k)) (L ω) := by
      dsimp only [L]
      rw [Matrix.spectralMeasure_def, empiricalMeasureOfFintype_toMeasure]
      exact integrable_finsetSum_measure.mpr fun _ _ ↦
        (integrable_dirac (by simp)).smul_measure (ENNReal.inv_ne_top.mpr (by simp))
    have hint_f : Integrable (fun x : ℝ ↦ 1 + x ^ (2 * k)) (L ω) :=
      (integrable_const (1 : ℝ)).add hint_pow
    have hint : ∫ x, (1 + x ^ (2 * k)) ∂L ω = 1 + ∫ x, x ^ (2 * k) ∂L ω := by
      rw [integral_add (integrable_const _) hint_pow, integral_const, probReal_univ, one_smul]
    rw [← hint, ofReal_integral_eq_lintegral_ofReal hint_f
      (.of_forall fun x ↦ (norm_nonneg (x ^ k)).trans (hdom_pt x))]
    exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hdom_pt x)
  have hint_Ω : Integrable (fun ω ↦ 1 + ∫ x, x ^ (2 * k) ∂L ω) P :=
    (integrable_const (1 : ℝ)).add
      (integrable_integral_pow_spectralMeasure_wignerMatrix hξp hηp n)
  have hnonneg_Ω (ω : Ω) : 0 ≤ 1 + ∫ x, x ^ (2 * k) ∂L ω :=
    add_nonneg zero_le_one (integral_nonneg fun x ↦ (even_two_mul k).pow_nonneg x)
  calc ∫⁻ ω, ∫⁻ x, ENNReal.ofReal ‖x ^ k‖ ∂L ω ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (1 + ∫ x, x ^ (2 * k) ∂L ω) ∂P := lintegral_mono hcomp
    _ = ENNReal.ofReal (∫ ω, (1 + ∫ x, x ^ (2 * k) ∂L ω) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint_Ω (.of_forall hnonneg_Ω)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end FixedSpace

section Convergence

/-- **Expected spectral moment convergence for triangular Wigner arrays.** For independent centered
entries on possibly varying probability spaces `(Ω n, P n)` whose `k`th absolute moments are
uniformly bounded by `B` and whose off-diagonal entries have common second absolute moment `s`,
the expected `k`th empirical spectral moment of `H_{n+1}` converges to the `k`th moment of
`semicircleReal 0 s` (for every `k : ℕ`). -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_of_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s) :
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
    exact abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) (hξsq n)
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hnat)
    refine squeeze_zero_norm (fun n ↦ ?_) hlim
    rw [Real.norm_eq_abs]
    exact abs_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n)

/-- **Expected spectral moment convergence for Wigner matrices.** On a single infinite entry array
with independent centered coordinates, uniformly bounded `k`th absolute moments, and common
off-diagonal second absolute moment `s`, the expected `k`th empirical spectral moment of `H_{n+1}`
converges to `∫ x ^ k ∂semicircleReal 0 s` (for every `k : ℕ`). -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix
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
  tendsto_integral_pow_spectralMeasure_wignerMatrix_of_array
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hηzero)
    (fun _ ↦ hξp) (fun _ ↦ hηp) (fun _ ↦ hξ) (fun _ ↦ hη) (fun _ ↦ hξsq)

/-- **Weak convergence of expected empirical spectral measures for triangular Wigner arrays.**
For independent centered entries on varying spaces `(Ω n, P n)` with common off-diagonal second
absolute moment `s` and uniformly bounded moments of every order, the expected empirical spectral
measures `(P n).bind L_{H_{n+1}}` converge weakly to `semicircleReal 0 s`. -/
theorem tendsto_bind_spectralMeasure_wignerMatrix_of_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ k n ij, MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ k n i, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n i, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ ⟨(P n).bind fun ω ↦ ((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ),
        have := (hindep n).isProbabilityMeasure
        isProbabilityMeasure_bind_spectralMeasure_wignerMatrix
          (fun ij ↦ (hξp 1 n ij).aestronglyMeasurable.aemeasurable)
          (fun i ↦ (hηp 1 n i).aestronglyMeasurable.aemeasurable) n⟩)
      atTop (𝓝 ⟨semicircleReal 0 s, inferInstance⟩) := by
  have hprob (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hξm (n : ℕ) (ij : StrictUpper) : AEMeasurable (ξ n ij) (P n) :=
    (hξp 1 n ij).aestronglyMeasurable.aemeasurable
  have hηm (n : ℕ) (i : ℕ) : AEMeasurable (η n i) (P n) :=
    (hηp 1 n i).aestronglyMeasurable.aemeasurable
  have hint (k n : ℕ) : Integrable (fun x : ℝ ↦ x ^ k)
      ((P n).bind fun ω ↦ ((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) :=
    integrable_pow_bind_spectralMeasure_wignerMatrix (hξp (2 * k) n) (hηp (2 * k) n) n
  refine ProbabilityMeasure.tendsto_of_tendsto_integral_pow
    (K := Set.Icc (0 - 2 * Real.sqrt s) (0 + 2 * Real.sqrt s)) isCompact_Icc
    (ae_iff.mp (ae_mem_Icc_semicircleReal 0 s))
    (fun k ↦ Eventually.of_forall fun n ↦ hint k n) fun k ↦ ?_
  obtain ⟨B₁, hB₁⟩ := hξ k
  obtain ⟨B₂, hB₂⟩ := hη k
  have hconv := tendsto_integral_pow_spectralMeasure_wignerMatrix_of_array (B := max B₁ B₂)
    hindep hξzero hηzero (hξp k) (hηp k)
    (fun n ij ↦ (hB₁ n ij).trans (le_max_left _ _))
    (fun n i ↦ (hB₂ n i).trans (le_max_right _ _)) hξsq
  refine hconv.congr fun n ↦ (Measure.integral_bind
    (aemeasurable_spectralMeasure_wignerMatrix (hξm n) (hηm n) n) (hint k n)).symm

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
          (fun ij ↦ (hξp 1 ij).aestronglyMeasurable.aemeasurable)
          (fun i ↦ (hηp 1 i).aestronglyMeasurable.aemeasurable) n⟩)
      atTop (𝓝 ⟨semicircleReal 0 s, inferInstance⟩) :=
  tendsto_bind_spectralMeasure_wignerMatrix_of_array
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hηzero)
    (fun k _ ↦ hξp k) (fun k _ ↦ hηp k)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ↦ hB⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ ↦ hB⟩)
    (fun _ ↦ hξsq)

/-- For any bounded continuous test function `f : ℝ →ᵇ ℝ` and triangular Wigner array satisfying
the moment hypotheses, `E[∫ f dL_{H_{n+1}}]` converges to `∫ f ∂semicircleReal 0 s`. -/
theorem tendsto_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix_of_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hξp : ∀ k n ij, MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ k n i, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n i, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s) (f : ℝ →ᵇ ℝ) :
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
    (fun ij ↦ (hξp 1 n ij).aestronglyMeasurable.aemeasurable)
    (fun i ↦ (hηp 1 n i).aestronglyMeasurable.aemeasurable) n
  have : IsProbabilityMeasure ((P n).bind fun ω ↦
      ((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) :=
    isProbabilityMeasure_bind_spectralMeasure_wignerMatrix
      (fun ij ↦ (hξp 1 n ij).aestronglyMeasurable.aemeasurable)
      (fun i ↦ (hηp 1 n i).aestronglyMeasurable.aemeasurable) n
  exact Measure.integral_bind hL (f.integrable _)

/-- For any bounded continuous test function `f : ℝ →ᵇ ℝ` on a single infinite Wigner array
satisfying the moment hypotheses, `E[∫ f dL_{H_{n+1}}]` converges to `∫ f ∂semicircleReal 0 s`. -/
theorem tendsto_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix
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
  tendsto_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix_of_array
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hηzero)
    (fun k _ ↦ hξp k) (fun k _ ↦ hηp k)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ↦ hB⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ ↦ hB⟩)
    (fun _ ↦ hξsq) f

end Convergence

end TauCeti.Probability
