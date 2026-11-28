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
import TauCeti.Probability.RandomMatrix.Wigner.Trace.Integrability

/-!
# Expected empirical spectral moments and expected semicircle law for Wigner matrices

For a Hermitian Wigner matrix `H_{n+1}`, the `k`th moment `∫ x ^ k dL_{H_{n+1}}` of its empirical
spectral measure is the real part of the normalized trace `(n + 1)⁻¹ tr(H_{n+1} ^ k)`. Against `P`,
this transfers the quantitative trace bounds from `TauCeti.Probability.RandomMatrix.MomentBounds`
and `TauCeti.Probability.RandomMatrix.LeadingMoments` directly to expected empirical spectral
moments. The transfer of `Lᵖ` bounds, integrability and expectations from traces to spectral
moments holds for every random Hermitian matrix of fixed size, and the Wigner versions are its
special cases. The quantitative consequences are:

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

* `TauCeti.Probability.memLp_integral_pow_spectralMeasure`,
  `TauCeti.Probability.integrable_integral_pow_spectralMeasure`, and
  `TauCeti.Probability.integral_integral_pow_spectralMeasure`: for a random Hermitian matrix, the
  `Lᵖ` bound, integrability and expectation of a spectral moment, from those of the trace.
* `TauCeti.Probability.integral_pow_spectralMeasure_wignerMatrix`,
  `TauCeti.Probability.integral_integral_pow_spectralMeasure_wignerMatrix`, and
  `TauCeti.Probability.integral_pow_bind_spectralMeasure_wignerMatrix`: deterministic, expected, and
  mixture spectral moments expressed through normalized traces; the mixture moments use `Lᵏ`
  corner entries.
* `TauCeti.Probability.memLp_integral_pow_spectralMeasure_wignerMatrix`: the `k`-th empirical
  spectral moment of `H_{n+1}` lies in `Lᵖ` under `L^(p * k)` corner entries.
* `TauCeti.Probability.abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le` and
  `TauCeti.Probability.abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le`:
  quantitative `O((n + 1)⁻¹)` and `O((√(n + 1))⁻¹)` error bounds against `semicircleReal 0 s`.
* `TauCeti.Probability.tendsto_integral_integral_pow_spectralMeasure_wignerMatrix'` and
  `TauCeti.Probability.tendsto_integral_integral_pow_spectralMeasure_wignerMatrix`: convergence of
  expected empirical spectral moments of every order `k : ℕ` to `semicircleReal 0 s`.
* `TauCeti.Probability.tendsto_bind_spectralMeasure_wignerMatrix'` and
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

section Hermitian

variable {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] {P : Measure Ω} [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [RCLike 𝕜] {A : Ω → Matrix ι ι 𝕜}

/-- If the trace of the `k`-th power of a random Hermitian matrix lies in `Lᵖ`, so does its `k`-th
empirical spectral moment. -/
theorem memLp_integral_pow_spectralMeasure (hA : ∀ ω, (A ω).IsHermitian) {p : ℝ≥0∞} {k : ℕ}
    (h : MemLp (fun ω ↦ (A ω ^ k).trace) p P) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((A ω).spectralMeasure (hA ω) : Measure ℝ)) p P := by
  simp_rw [Matrix.integral_pow_spectralMeasure]
  exact h.re.const_mul _

/-- If the trace of the `k`-th power of a random Hermitian matrix is integrable, so is its `k`-th
empirical spectral moment. -/
theorem integrable_integral_pow_spectralMeasure (hA : ∀ ω, (A ω).IsHermitian) {k : ℕ}
    (h : Integrable (fun ω ↦ (A ω ^ k).trace) P) :
    Integrable (fun ω ↦ ∫ x, x ^ k ∂((A ω).spectralMeasure (hA ω) : Measure ℝ)) P :=
  memLp_one_iff_integrable.1 <|
    memLp_integral_pow_spectralMeasure hA (memLp_one_iff_integrable.2 h)

/-- The expected `k`-th empirical spectral moment of a random Hermitian matrix is the real part of
its normalized expected `k`-th trace. No moment or finiteness hypothesis is needed: the trace of a
power of a Hermitian matrix is real, and the Bochner integral commutes with the embedding of `ℝ`
in `𝕜`. -/
theorem integral_integral_pow_spectralMeasure (hA : ∀ ω, (A ω).IsHermitian) (k : ℕ) :
    ∫ ω, (∫ x, x ^ k ∂((A ω).spectralMeasure (hA ω) : Measure ℝ)) ∂P =
      RCLike.re (((Fintype.card ι : ℕ) : 𝕜)⁻¹ * ∫ ω, (A ω ^ k).trace ∂P) := by
  have h (ω : Ω) : ((Fintype.card ι : ℕ) : 𝕜)⁻¹ * (A ω ^ k).trace =
      RCLike.ofReal (∫ x, x ^ k ∂((A ω).spectralMeasure (hA ω) : Measure ℝ)) :=
    (Matrix.ofReal_integral_pow_spectralMeasure _ (hA ω) k).symm
  rw [← integral_const_mul]
  simp_rw [h]
  rw [integral_ofReal, RCLike.ofReal_re]

end Hermitian

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

/-- If the entries in the `(n + 1) × (n + 1)` corner of the Wigner array lie in `L^(p * k)`, the
`k`-th empirical spectral moment of `Hₙ₊₁` lies in `Lᵖ` for every `p : ℝ≥0∞`, without
independence or centering. The measure is assumed finite when `k = 0`. -/
theorem memLp_integral_pow_spectralMeasure_wignerMatrix {p : ℝ≥0∞} {k : ℕ}
    (hP : k = 0 → IsFiniteMeasure P) (n : ℕ)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (p * k) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (p * k) P) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) p P :=
  memLp_integral_pow_spectralMeasure _ (memLp_trace_pow_wignerMatrix hP hξp hηp)

/-- The `k`th empirical spectral moment of the `(n + 1) × (n + 1)` Wigner matrix is integrable
whenever all coordinates in the `(n + 1) × (n + 1)` corner lie in `Lᵏ`. The measure is assumed
finite when `k = 0`. -/
theorem integrable_integral_pow_spectralMeasure_wignerMatrix {k n : ℕ}
    (hP : k = 0 → IsFiniteMeasure P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) k P)
    (hη : ∀ i < n + 1, MemLp (η i) k P) :
    Integrable (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P :=
  integrable_integral_pow_spectralMeasure _ (integrable_trace_pow_wignerMatrix hP hξ hη)

/-- The expected `k`th empirical spectral moment is the real part of the normalized expected `k`th
trace. No moment or finiteness hypothesis is needed: the trace of a power of a Hermitian matrix is
real, and the Bochner integral commutes with the embedding of `ℝ` in `ℂ`. -/
theorem integral_integral_pow_spectralMeasure_wignerMatrix (n k : ℕ) :
    ∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P =
      (((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ k).trace ∂P).re := by
  rw [integral_integral_pow_spectralMeasure, Fintype.card_fin, RCLike.re_to_complex]

/-- **Quantitative expected even spectral moment bound.** For independent entries in the
`(n + 1) × (n + 1)` corner with `2m`th absolute moments bounded by `B` and centered strictly upper
entries of second absolute moment `s`, the expected `2m`th empirical spectral moment of `H_{n+1}`
lies within `O((n + 1)⁻¹)` of the `2m`th moment of `semicircleReal 0 s` (for every `m n : ℕ`).
Diagonal entries need not be centered. -/
theorem abs_integral_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_le
    {m n : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B)
    (hξsq : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    |(∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) -
      ∫ x, x ^ (2 * m) ∂semicircleReal 0 s| ≤
      ((m : ℝ) ^ (2 * m) * B + (s : ℝ) ^ m * catalan m * (m + 1).choose 2) / (n + 1 : ℕ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [integral_integral_pow_spectralMeasure_wignerMatrix,
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
          (Nat.add_one_ne_zero n) s.coe_nonneg hindep hξzero hξp hηp hξ hη hξsq

/-- **Quantitative expected odd spectral moment bound.** For independent entries in the
`(n + 1) × (n + 1)` corner with centered strictly upper coordinates and `(2m + 1)`st absolute
moments bounded by `B`, the expected `(2m + 1)`st empirical spectral moment of `H_{n+1}` has
magnitude at most `(m + 1) ^ (2 * m + 1) * B / √(n + 1)`. Diagonal entries need not be centered. -/
theorem abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
    {m n : ℕ} {B : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i < n + 1, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i < n + 1, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [integral_integral_pow_spectralMeasure_wignerMatrix]
  exact (Complex.abs_re_le_norm _).trans
    (norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le
      hindep hξzero hξp hηp hξ hη)

/-- The empirical spectral measure of the `(n + 1) × (n + 1)` Wigner matrix, viewed as a random
measure on `ℝ`, is almost everywhere measurable whenever the corner entry coordinates are. -/
theorem aemeasurable_spectralMeasure_wignerMatrix {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, AEMeasurable (η i) P) :
    AEMeasurable (fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P := by
  have hH : AEMeasurable (Set.codRestrict (wignerMatrix ξ η (n + 1)) {A | A.IsHermitian}
      fun ω ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) P :=
    (aemeasurable_wignerMatrix hξ hη).subtype_mk
  exact (measurable_subtypeVal.comp Matrix.measurable_spectralMeasure).comp_aemeasurable hH

/-- On a probability space, the mixture `P.bind L_{H_{n+1}}` — the expected empirical spectral
measure of the Wigner matrix — is a probability measure whenever the corner entry coordinates are
almost everywhere measurable. -/
theorem isProbabilityMeasure_bind_spectralMeasure_wignerMatrix [IsProbabilityMeasure P] {n : ℕ}
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, AEMeasurable (η i) P) :
    IsProbabilityMeasure (P.bind fun ω ↦ ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) :=
  isProbabilityMeasure_bind (aemeasurable_spectralMeasure_wignerMatrix hξ hη)
    (.of_forall fun _ ↦ inferInstance)

/-- On a finite measure space, the monomial `x ↦ x ^ k` is integrable against the expected
empirical spectral measure `P.bind L_{H_{n+1}}` whenever the corner entry coordinates lie in
`Lᵏ`. -/
theorem integrable_pow_bind_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k n : ℕ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (k : ℕ) P)
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
  let M : Ω → ℝ := fun ω ↦
    (Fintype.card (Fin (n + 1)) : ℝ) *
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ‖wignerMatrix ξ η (n + 1) ω i j‖
  have hM : MemLp M (k : ℕ) P :=
    (memLp_finsetSum Finset.univ fun i _ ↦
      memLp_finsetSum Finset.univ fun j _ ↦
        (memLp_wignerMatrix_apply hξp hηp i j).norm).const_mul _
  have hM_nonneg (ω : Ω) : 0 ≤ M ω := by
    dsimp only [M]
    positivity
  calc ∫⁻ ω, ∫⁻ x, ENNReal.ofReal ‖x ^ k‖ ∂L ω ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (M ω ^ k) ∂P :=
        lintegral_mono fun ω ↦
          Matrix.lintegral_ofReal_norm_pow_spectralMeasure_le _
            (wignerMatrix_isHermitian ξ η ω (n + 1)) k
    _ = ∫⁻ ω, ENNReal.ofReal (‖M ω‖ ^ k) ∂P := by
        simp_rw [Real.norm_of_nonneg (hM_nonneg _)]
    _ = ENNReal.ofReal (∫ ω, ‖M ω‖ ^ k ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hM.integrable_norm_pow'
          (.of_forall fun _ ↦ by positivity)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- On a finite measure space with `Lᵏ` corner entries, the `k`th moment of the expected empirical
spectral measure `P.bind L_{H_{n+1}}` equals the expected `k`th empirical spectral moment. -/
theorem integral_pow_bind_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k n : ℕ}
    (hξp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) (k : ℕ) P)
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

/-- **Expected spectral moment convergence for triangular Wigner arrays.** For independent entries
in the `(n + 1) × (n + 1)` corner on possibly varying probability spaces `(Ω n, P n)` whose `k`th
absolute moments are uniformly bounded by `B` and whose strictly upper entries are centered with
common second absolute moment `s`, the expected `k`th empirical spectral moment of `H_{n+1}`
converges to the `k`th moment of `semicircleReal 0 s` (for every `k : ℕ`). -/
theorem tendsto_integral_integral_pow_spectralMeasure_wignerMatrix'
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ n, ∀ i < n + 1, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s) :
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
      (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n) (hξsq n)
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hnat)
    refine squeeze_zero_norm (fun n ↦ ?_) hlim
    rw [Real.norm_eq_abs]
    exact abs_integral_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
      (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n)

/-- **Expected spectral moment convergence for Wigner matrices.** On a single infinite entry array
with independent coordinates, centered off-diagonal entries of common second absolute moment `s`,
and uniformly bounded `k`th absolute moments, the expected `k`th empirical spectral moment of
`H_{n+1}` converges to `∫ x ^ k ∂semicircleReal 0 s` (for every `k : ℕ`). -/
theorem tendsto_integral_integral_pow_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k : ℕ} {B : ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (k : ℕ) P) (hηp : ∀ i, MemLp (η i) (k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k
        ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 s)) :=
  tendsto_integral_integral_pow_spectralMeasure_wignerMatrix'
    (fun _ ↦ iIndepFun_sumElim_ofReal_subtype_lt hindep)
    (fun _ ij _ ↦ hξzero ij)
    (fun _ ij _ ↦ hξp ij) (fun _ i _ ↦ hηp i)
    (fun _ ij _ ↦ hξ ij) (fun _ i _ ↦ hη i) (fun _ ij _ ↦ hξsq ij)

/-- **Weak convergence of expected empirical spectral measures for triangular Wigner arrays.**
For independent corner entries on varying spaces `(Ω n, P n)` with centered strictly upper entries
of common second absolute moment `s` and uniformly bounded moments of every order, the expected
empirical spectral measures `(P n).bind L_{H_{n+1}}` converge weakly to `semicircleReal 0 s`. -/
theorem tendsto_bind_spectralMeasure_wignerMatrix'
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ k n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ k n, ∀ i < n + 1, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s) :
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
      integrable_pow_bind_spectralMeasure_wignerMatrix (hξp (2 * k) n) (hηp (2 * k) n))
    fun k ↦ ?_
  obtain ⟨B₁, hB₁⟩ := hξ k
  obtain ⟨B₂, hB₂⟩ := hη k
  have hconv := tendsto_integral_integral_pow_spectralMeasure_wignerMatrix'
    (B := max B₁ B₂) hindep hξzero (hξp k) (hηp k)
    (fun n ij hij ↦ (hB₁ n ij hij).trans (le_max_left _ _))
    (fun n i hi ↦ (hB₂ n i hi).trans (le_max_right _ _)) hξsq
  exact hconv.congr fun n ↦
    (integral_pow_bind_spectralMeasure_wignerMatrix (hξp k n) (hηp k n)).symm

/-- **Weak convergence of the expected empirical spectral measure for Wigner matrices.**
On a single infinite entry array with independent coordinates, centered off-diagonal entries of
common second absolute moment `s`, and uniformly bounded moments of every order,
`P.bind L_{H_{n+1}}` converges weakly to `semicircleReal 0 s`. -/
theorem tendsto_bind_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {s : ℝ≥0}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
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
  tendsto_bind_spectralMeasure_wignerMatrix'
    (fun _ ↦ iIndepFun_sumElim_ofReal_subtype_lt hindep)
    (fun _ ij _ ↦ hξzero ij)
    (fun k _ ij _ ↦ hξp k ij) (fun k _ i _ ↦ hηp k i)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ij _ ↦ hB ij⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ i _ ↦ hB i⟩)
    (fun _ ij _ ↦ hξsq ij)

/-- For any bounded continuous test function `f : ℝ →ᵇ ℝ` and triangular Wigner array satisfying
the corner moment hypotheses, `E[∫ f dL_{H_{n+1}}]` converges to `∫ f ∂semicircleReal 0 s`. -/
theorem tendsto_integral_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix'
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ} {s : ℝ≥0}
    (hindep : ∀ n, iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n + 1} ⊕ {i : ℕ // i < n + 1} ↦
        Sum.elim (fun ij ↦ ξ n ij.val) (fun i ω ↦ (η n i.val ω : ℂ)) r) (P n))
    (hξzero : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ k n (ij : StrictUpper), ij.val.2 < n + 1 → MemLp (ξ n ij) (k : ℕ) (P n))
    (hηp : ∀ k n, ∀ i < n + 1, MemLp (η n i) (k : ℕ) (P n))
    (hξ : ∀ k, ∃ B, ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ k, ∃ B, ∀ n, ∀ i < n + 1, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B)
    (hξsq : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = s)
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, f x
        ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, f x ∂semicircleReal 0 s)) := by
  have hweak := tendsto_bind_spectralMeasure_wignerMatrix'
    hindep hξzero hξp hηp hξ hη hξsq
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
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ k ij, MemLp (ξ ij) (k : ℕ) P) (hηp : ∀ k i, MemLp (η i) (k : ℕ) P)
    (hξ : ∀ k, ∃ B, ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B)
    (hη : ∀ k, ∃ B, ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, f x
        ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 (∫ x, f x ∂semicircleReal 0 s)) :=
  tendsto_integral_integral_boundedContinuousFunction_spectralMeasure_wignerMatrix'
    (fun _ ↦ iIndepFun_sumElim_ofReal_subtype_lt hindep)
    (fun _ ij _ ↦ hξzero ij)
    (fun k _ ij _ ↦ hξp k ij) (fun k _ i _ ↦ hηp k i)
    (fun k ↦ let ⟨B, hB⟩ := hξ k; ⟨B, fun _ ij _ ↦ hB ij⟩)
    (fun k ↦ let ⟨B, hB⟩ := hη k; ⟨B, fun _ i _ ↦ hB i⟩)
    (fun _ ij _ ↦ hξsq ij) f

end Convergence

end TauCeti.Probability
