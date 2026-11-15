/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SpectralMoment.Catalan
public import TauCeti.Probability.Moments.Variance
public import TauCeti.Probability.Moments.WeakConvergence
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Higher-moment concentration and Wigner's semicircle law under bounded moments

Expanding `Var[n⁻¹ Re tr(Hₙᵏ)]` into a sum over pairs `(w₁, w₂)` of closed walks of length `k`
cancels every pair with disjoint edge sets by independence
(`indepFun_prod_wignerMatrix_apply_of_ne`) and vanishes on every pair whose combined `2 * k`-step
edge multiset contains a singleton nonloop edge (`integral_prod_wignerMatrix_apply_eq_zero_of_ne`).
Every surviving pair shares at least one edge and has no combined singleton nonloop edge, so by
`card_union_image_le_of_shared_edge_of_no_singleton_nonloop_edge` it visits at most `k` distinct
vertices in total. There are at most `n ^ k * k ^ (2 * k)` such pairs, and each pair contributes at
most `2 * n⁻¹ ^ k * B` under a uniform `2 * k`-th moment bound `B`, yielding the summable `O(n⁻²)`
variance bound `2 * k ^ (2 * k) * B / n ^ 2`.

Combining this variance bound with Chebyshev's inequality, the first Borel–Cantelli lemma, the
expected spectral-moment convergence (`tendsto_integral_spectralMoment_wignerMatrix`), and the
method of moments (`ProbabilityMeasure.tendsto_of_tendsto_integral_pow`) establishes:

* `TauCeti.variance_inv_mul_re_trace_pow_wignerMatrix_le`: `O(n⁻²)` variance bound for normalized
  real traces of Wigner matrix powers, without diagonal centering or second-moment normalization.
* `TauCeti.Probability.variance_spectralMoment_wignerMatrix_le` and
  `TauCeti.Probability.measure_spectralMoment_wignerMatrix_sub_mean_ge`: `O((n + 1)⁻²)` variance
  and Chebyshev tail bounds for empirical spectral moments.
* `TauCeti.Probability.tendsto_spectralMoment_wignerMatrix_probability`: convergence in probability
  of `k`-th empirical spectral moments for triangular Wigner arrays under `2 * k`-th moment bounds.
* `TauCeti.Probability.ae_tendsto_spectralMoment_wignerMatrix`: almost-sure convergence of the
  `k`-th empirical spectral moment to the `k`-th semicircle moment under `2 * k`-th moment bounds.
* `TauCeti.Probability.ae_tendsto_spectralMeasure_wignerMatrix` and
  `TauCeti.Probability.ae_tendsto_integral_spectralMeasure_wignerMatrix`: almost-sure weak
  convergence of the empirical spectral measures to `semicircleReal 0 1` when all positive even
  coordinate moments are uniformly bounded.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.7 and Theorem 2.1.1.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter TauCeti.TreeWalk
open scoped Topology ENNReal BoundedContinuousFunction

namespace TauCeti

private theorem memLp_and_integral_norm_pow_le_sqrt {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → E}
    {k : ℕ} (hk : k ≠ 0) {B : ℝ} (hfp : MemLp f (2 * k : ℕ) P)
    (hfB : ∫ ω, ‖f ω‖ ^ (2 * k) ∂P ≤ B) :
    MemLp f k P ∧ ∫ ω, ‖f ω‖ ^ k ∂P ≤ √B := by
  refine ⟨hfp.mono_exponent (by norm_cast; omega), ?_⟩
  have hsq : (fun ω ↦ ‖‖f ω‖ ^ k‖ ^ 2) = fun ω ↦ ‖f ω‖ ^ (2 * k) := by
    ext ω
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) k), ← pow_mul, mul_comm]
  have hg : MemLp (fun ω ↦ ‖f ω‖ ^ k) 2 P :=
    (memLp_two_iff_integrable_sq_norm (hfp.aestronglyMeasurable.norm.pow k)).2
      (hsq ▸ hfp.integrable_norm_pow (by positivity))
  exact (integral_le_sqrt_integral_sq hg).trans (by
    simpa only [← pow_mul, mul_comm k 2] using Real.sqrt_le_sqrt hfB)

section TraceVariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

private noncomputable def wordProd (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    {k n : ℕ} (w : Fin k → Fin n) (ω : Ω) : ℂ :=
  ∏ t : Fin k, wignerMatrix ξ η n ω (w t) (w (finRotate k t))

private noncomputable def wordCov (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (P : Measure Ω) {k n : ℕ} (w₁ w₂ : Fin k → Fin n) : ℂ :=
  (∫ ω, wordProd ξ η w₁ ω * wordProd ξ η w₂ ω ∂P) -
    (∫ ω, wordProd ξ η w₁ ω ∂P) * (∫ ω, wordProd ξ η w₂ ω ∂P)

omit [MeasurableSpace Ω] in
private theorem wordProd_mul_eq_prod_sum {k n : ℕ} (w₁ w₂ : Fin k → Fin n) (ω : Ω) :
    wordProd ξ η w₁ ω * wordProd ξ η w₂ ω =
      ∏ x : Fin k ⊕ Fin k, wignerMatrix ξ η n ω
        (Sum.elim w₁ w₂ x) (Sum.elim (w₁ ∘ finRotate k) (w₂ ∘ finRotate k) x) := by
  rw [Fintype.prod_sum_type]
  rfl

private theorem integrable_wordProd_mul [IsFiniteMeasure P] {k n : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (w₁ w₂ : Fin k → Fin n) :
    Integrable (fun ω ↦ wordProd ξ η w₁ ω * wordProd ξ η w₂ ω) P := by
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  simp_rw [wordProd_mul_eq_prod_sum]
  exact integrable_prod_wignerMatrix_apply (by simpa [hcard] using hξp)
    (by simpa [hcard] using hηp) _ _

/-- On a finite measure space, the normalized real trace of the `k`-th power of a Wigner matrix
belongs to `L²` whenever all coordinates belong to `L²ᵏ`. -/
theorem memLp_two_inv_mul_re_trace_pow_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ (n : ℝ)⁻¹ * ((wignerMatrix ξ η n ω ^ k).trace).re) 2 P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [pow_zero, trace_one, Fintype.card_fin]
    exact memLp_const _
  · have hξk : ∀ ij, MemLp (ξ ij) k P := fun ij ↦ (hξp ij).mono_exponent (by norm_cast; omega)
    have hηk : ∀ i, MemLp (η i) k P := fun i ↦ (hηp i).mono_exponent (by norm_cast; omega)
    have haesm : AEStronglyMeasurable
        (fun ω ↦ (n : ℝ)⁻¹ * ((wignerMatrix ξ η n ω ^ k).trace).re) P := by
      simpa only [RCLike.re_to_complex] using
        ((integrable_trace_pow_wignerMatrix hξk hηk n).re.const_mul (n : ℝ)⁻¹).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm haesm).2 ?_
    have hsq (ω : Ω) : ‖(n : ℝ)⁻¹ * ((wignerMatrix ξ η n ω ^ k).trace).re‖ ^ 2 =
        (n : ℝ)⁻¹ ^ 2 * (∑ p : (Fin k → Fin n) × (Fin k → Fin n),
          wordProd ξ η p.1 ω * wordProd ξ η p.2 ω).re := by
      have hc : (((wignerMatrix ξ η n ω ^ k).trace).re : ℂ) =
          ∑ w : Fin k → Fin n, wordProd ξ η w ω := by
        rw [ofReal_re_trace_pow_wignerMatrix, trace_pow_eq_sum_prod _ hk]; rfl
      have hre : (((wignerMatrix ξ η n ω ^ k).trace).re) ^ 2 =
          (∑ p : (Fin k → Fin n) × (Fin k → Fin n),
            wordProd ξ η p.1 ω * wordProd ξ η p.2 ω).re := by
        calc (((wignerMatrix ξ η n ω ^ k).trace).re) ^ 2
            = (((((wignerMatrix ξ η n ω ^ k).trace).re : ℂ) ^ 2)).re := by
              rw [← Complex.ofReal_pow, Complex.ofReal_re]
          _ = _ := by rw [hc, sq, sum_mul_sum, ← sum_product', univ_product_univ]
      rw [Real.norm_eq_abs, sq_abs, mul_pow, hre]
    simp_rw [hsq]
    simpa only [RCLike.re_to_complex] using
      ((integrable_finsetSum (univ : Finset ((Fin k → Fin n) × (Fin k → Fin n))) fun p _ ↦
        integrable_wordProd_mul hξp hηp p.1 p.2).re).const_mul _

private theorem variance_re_trace_eq_re_sum_wordCov [IsProbabilityMeasure P] {k : ℕ} (hk : k ≠ 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    Var[fun ω ↦ (n : ℝ)⁻¹ * ((wignerMatrix ξ η n ω ^ k).trace).re; P] =
      (n : ℝ)⁻¹ ^ 2 *
        (∑ p : (Fin k → Fin n) × (Fin k → Fin n), wordCov ξ η P p.1 p.2).re := by
  let T : Ω → ℝ := fun ω ↦ (n : ℝ)⁻¹ * ((wignerMatrix ξ η n ω ^ k).trace).re
  have hξk : ∀ ij, MemLp (ξ ij) k P := fun ij ↦ (hξp ij).mono_exponent (by norm_cast; omega)
  have hηk : ∀ i, MemLp (η i) k P := fun i ↦ (hηp i).mono_exponent (by norm_cast; omega)
  have hwp_int (w : Fin k → Fin n) : Integrable (wordProd ξ η w) P :=
    integrable_prod_wignerMatrix_apply (by simpa using hξk) (by simpa using hηk) _ _
  have hsq_sum (f : (Fin k → Fin n) → ℂ) :
      ((n : ℂ)⁻¹ * ∑ w : Fin k → Fin n, f w) ^ 2 =
        ((n : ℝ)⁻¹ ^ 2 : ℝ) * ∑ p : (Fin k → Fin n) × (Fin k → Fin n), f p.1 * f p.2 := by
    rw [mul_pow, sq (∑ w, f w), sum_mul_sum, ← sum_product', univ_product_univ]
    simp
  have hT_coe (ω : Ω) : (T ω : ℂ) = (n : ℂ)⁻¹ * ∑ w : Fin k → Fin n, wordProd ξ η w ω := by
    dsimp only [T]
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      ofReal_re_trace_pow_wignerMatrix, trace_pow_eq_sum_prod _ hk]
    rfl
  have hT_sq (ω : Ω) : T ω ^ 2 = (n : ℝ)⁻¹ ^ 2 *
      (∑ p : (Fin k → Fin n) × (Fin k → Fin n),
        wordProd ξ η p.1 ω * wordProd ξ η p.2 ω).re := by
    have h := congrArg (fun z : ℂ ↦ (z ^ 2).re) (hT_coe ω)
    rw [← Complex.ofReal_pow, Complex.ofReal_re, hsq_sum, Complex.re_ofReal_mul] at h
    exact h
  have hmean_coe : ((∫ ω, T ω ∂P : ℝ) : ℂ) =
      (n : ℂ)⁻¹ * ∑ w : Fin k → Fin n, ∫ ω, wordProd ξ η w ω ∂P := by
    rw [← integral_complex_ofReal, integral_congr_ae (.of_forall hT_coe), integral_const_mul,
      integral_finsetSum _ fun w _ ↦ hwp_int w]
  have hmean_sq : (∫ ω, T ω ∂P) ^ 2 = (n : ℝ)⁻¹ ^ 2 *
      (∑ p : (Fin k → Fin n) × (Fin k → Fin n),
        (∫ ω, wordProd ξ η p.1 ω ∂P) * (∫ ω, wordProd ξ η p.2 ω ∂P)).re := by
    have h := congrArg (fun z : ℂ ↦ (z ^ 2).re) hmean_coe
    rw [← Complex.ofReal_pow, Complex.ofReal_re, hsq_sum, Complex.re_ofReal_mul] at h
    exact h
  change Var[T; P] = _
  rw [ProbabilityTheory.variance_eq_sub (memLp_two_inv_mul_re_trace_pow_wignerMatrix hξp hηp n)]
  have hint_sq : ∫ ω, (T ^ 2) ω ∂P = (n : ℝ)⁻¹ ^ 2 *
      (∑ p : (Fin k → Fin n) × (Fin k → Fin n),
        ∫ ω, wordProd ξ η p.1 ω * wordProd ξ η p.2 ω ∂P).re := by
    simp_rw [Pi.pow_apply, hT_sq]
    rw [integral_const_mul]
    congr 1
    simp_rw [← Complex.reCLM_apply]
    rw [Complex.reCLM.integral_comp_comm
      (integrable_finsetSum (univ : Finset ((Fin k → Fin n) × (Fin k → Fin n))) fun p _ ↦
        integrable_wordProd_mul hξp hηp p.1 p.2),
      integral_finsetSum (univ : Finset ((Fin k → Fin n) × (Fin k → Fin n))) fun p _ ↦
        integrable_wordProd_mul hξp hηp p.1 p.2]
  rw [hint_sq, hmean_sq, ← mul_sub, ← Complex.sub_re, ← sum_sub_distrib]
  rfl

private def IsSurvivingWordPair {k n : ℕ} (p : (Fin k → Fin n) × (Fin k → Fin n)) : Prop :=
  (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))) ∧
  ∀ x : Fin k ⊕ Fin k,
    Sum.elim p.1 p.2 x ≠ Sum.elim (p.1 ∘ finRotate k) (p.2 ∘ finRotate k) x →
    ∃ y ≠ x,
      Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
        (fun t ↦ s(p.2 t, p.2 (finRotate k t))) y =
      Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
        (fun t ↦ s(p.2 t, p.2 (finRotate k t))) x

private theorem wordCov_eq_zero_of_disjoint_edges {k n : ℕ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξk : ∀ ij, MemLp (ξ ij) k P) (hηk : ∀ i, MemLp (η i) k P)
    {w₁ w₂ : Fin k → Fin n}
    (hdisj : ∀ t₁ t₂, s(w₁ t₁, w₁ (finRotate k t₁)) ≠ s(w₂ t₂, w₂ (finRotate k t₂))) :
    wordCov ξ η P w₁ w₂ = 0 := by
  have := hindep.isProbabilityMeasure
  have hind := indepFun_prod_wignerMatrix_apply_of_ne
    (fun ij ↦ (hξk ij).aestronglyMeasurable.aemeasurable)
    (fun i ↦ (hηk i).aestronglyMeasurable.aemeasurable)
    hindep w₁ (w₁ ∘ finRotate k) w₂ (w₂ ∘ finRotate k) hdisj
  have hae₁ := (integrable_prod_wignerMatrix_apply (by simpa using hξk) (by simpa using hηk)
    w₁ (w₁ ∘ finRotate k)).aestronglyMeasurable
  have hae₂ := (integrable_prod_wignerMatrix_apply (by simpa using hξk) (by simpa using hηk)
    w₂ (w₂ ∘ finRotate k)).aestronglyMeasurable
  exact sub_eq_zero.mpr (hind.integral_fun_mul_eq_mul_integral hae₁ hae₂)

private theorem wordCov_eq_zero_of_not_surviving {k n : ℕ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    {w₁ w₂ : Fin k → Fin n} (hnot : ¬ IsSurvivingWordPair (w₁, w₂)) :
    wordCov ξ η P w₁ w₂ = 0 := by
  have := hindep.isProbabilityMeasure
  have hξm (ij : StrictUpper) := (hξp ij).aestronglyMeasurable.aemeasurable
  have hηm (i : ℕ) := (hηp i).aestronglyMeasurable.aemeasurable
  have hξk : ∀ ij, MemLp (ξ ij) k P := fun ij ↦ (hξp ij).mono_exponent (by norm_cast; omega)
  have hηk : ∀ i, MemLp (η i) k P := fun i ↦ (hηp i).mono_exponent (by norm_cast; omega)
  by_cases hshare : ∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂))
  · obtain ⟨x, hx⟩ := Classical.not_forall.mp fun h' ↦ hnot ⟨hshare, h'⟩
    rw [not_imp] at hx
    obtain ⟨hx_ne, hx_not⟩ := hx
    have hx_only (y : Fin k ⊕ Fin k) (hy :
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate k t))) y =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate k t))) x) : y = x :=
      by_contra fun hyx ↦ hx_not ⟨y, hyx, hy⟩
    have hedge (z : Fin k ⊕ Fin k) :
        s(Sum.elim w₁ w₂ z, Sum.elim (w₁ ∘ finRotate k) (w₂ ∘ finRotate k) z) =
          Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
            (fun t ↦ s(w₂ t, w₂ (finRotate k t))) z := by cases z <;> rfl
    have hprod0 : ∫ ω, wordProd ξ η w₁ ω * wordProd ξ η w₂ ω ∂P = 0 := by
      simp_rw [wordProd_mul_eq_prod_sum]
      exact integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero _ _ hx_ne
        fun y hy ↦ hx_only y (by simpa only [hedge] using hy)
    have hfac0 : (∫ ω, wordProd ξ η w₁ ω ∂P) * (∫ ω, wordProd ξ η w₂ ω ∂P) = 0 := by
      cases x with
      | inl t₁ =>
        have h0 : ∫ ω, wordProd ξ η w₁ ω ∂P = 0 :=
          integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero w₁
            (w₁ ∘ finRotate k) (by simpa using hx_ne)
            (fun s hs ↦ Sum.inl.inj (hx_only (.inl s) hs))
        rw [h0, zero_mul]
      | inr t₂ =>
        have h0 : ∫ ω, wordProd ξ η w₂ ω ∂P = 0 :=
          integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero w₂
            (w₂ ∘ finRotate k) (by simpa using hx_ne)
            (fun s hs ↦ Sum.inr.inj (hx_only (.inr s) hs))
        rw [h0, mul_zero]
    simp [wordCov, hprod0, hfac0]
  · exact wordCov_eq_zero_of_disjoint_edges hindep hξk hηk fun t₁ t₂ h ↦ hshare ⟨t₁, t₂, h⟩

private theorem norm_wordCov_le [IsProbabilityMeasure P] {k n : ℕ} (hk : k ≠ 0) {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w₁ w₂ : Fin k → Fin n) :
    ‖wordCov ξ η P w₁ w₂‖ ≤ 2 * (n : ℝ)⁻¹ ^ k * B := by
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) (2 * k)).trans (hη 0)
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  have hsqrt_pow : (Real.sqrt n)⁻¹ ^ (2 * k) = (n : ℝ)⁻¹ ^ k := by
    rw [inv_pow, inv_pow, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
  have h1 : ‖∫ ω, wordProd ξ η w₁ ω * wordProd ξ η w₂ ω ∂P‖ ≤ (n : ℝ)⁻¹ ^ k * B := by
    simp_rw [wordProd_mul_eq_prod_sum]
    simpa [hcard, hsqrt_pow] using norm_integral_prod_wignerMatrix_apply_le
      (by simpa [hcard] using hξp) (by simpa [hcard] using hηp)
      (by simpa [hcard] using hξ) (by simpa [hcard] using hη)
      (Sum.elim w₁ w₂) (Sum.elim (w₁ ∘ finRotate k) (w₂ ∘ finRotate k))
  have hξk := fun ij ↦ memLp_and_integral_norm_pow_le_sqrt hk (hξp ij) (hξ ij)
  have hηk := fun i ↦ memLp_and_integral_norm_pow_le_sqrt hk (hηp i) (hη i)
  have hw_le (w : Fin k → Fin n) : ‖∫ ω, wordProd ξ η w ω ∂P‖ ≤ (Real.sqrt n)⁻¹ ^ k * √B := by
    simpa [wordProd] using norm_integral_prod_wignerMatrix_apply_le
      (by simpa using fun ij ↦ (hξk ij).1) (by simpa using fun i ↦ (hηk i).1)
      (by simpa using fun ij ↦ (hξk ij).2) (by simpa using fun i ↦ (hηk i).2)
      w (w ∘ finRotate k)
  have h2 : ‖(∫ ω, wordProd ξ η w₁ ω ∂P) * (∫ ω, wordProd ξ η w₂ ω ∂P)‖ ≤ (n : ℝ)⁻¹ ^ k * B := by
    rw [norm_mul]
    calc _ ≤ ((Real.sqrt n)⁻¹ ^ k * √B) * ((Real.sqrt n)⁻¹ ^ k * √B) :=
          mul_le_mul (hw_le w₁) (hw_le w₂) (norm_nonneg _) (by positivity)
      _ = (Real.sqrt n)⁻¹ ^ (2 * k) * (√B * √B) := by rw [two_mul, pow_add]; ring
      _ = (n : ℝ)⁻¹ ^ k * B := by rw [hsqrt_pow, Real.mul_self_sqrt hB]
  calc ‖wordCov ξ η P w₁ w₂‖
      ≤ ‖∫ ω, wordProd ξ η w₁ ω * wordProd ξ η w₂ ω ∂P‖ +
          ‖(∫ ω, wordProd ξ η w₁ ω ∂P) * (∫ ω, wordProd ξ η w₂ ω ∂P)‖ := norm_sub_le _ _
    _ ≤ (n : ℝ)⁻¹ ^ k * B + (n : ℝ)⁻¹ ^ k * B := add_le_add h1 h2
    _ = 2 * (n : ℝ)⁻¹ ^ k * B := by ring

private theorem card_survivingWordPairs_le {k n : ℕ} (hn : n ≠ 0)
    (Surv : Finset ((Fin k → Fin n) × (Fin k → Fin n)))
    (hSurv : ∀ p ∈ Surv, IsSurvivingWordPair p) :
    #Surv ≤ n ^ k * k ^ (2 * k) := by
  have : NeZero n := ⟨hn⟩
  let e : (Fin k → Fin n) × (Fin k → Fin n) ≃ (Fin k ⊕ Fin k → Fin n) :=
    (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (Fin n)).symm
  have himg (p : (Fin k → Fin n) × (Fin k → Fin n)) :
      (univ : Finset (Fin k ⊕ Fin k)).image (e p) = univ.image p.1 ∪ univ.image p.2 := by
    ext v
    simp only [mem_union, mem_image, mem_univ, true_and, Sum.exists]
    rfl
  calc #Surv = #(Surv.map e.toEmbedding) := (card_map _).symm
    _ ≤ #{f : Fin k ⊕ Fin k → Fin n | #(univ.image f) ≤ k} := by
      refine card_le_card fun f hf ↦ ?_
      obtain ⟨p, hp, rfl⟩ := mem_map.mp hf
      obtain ⟨hshare, hns⟩ := hSurv p hp
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      change #(univ.image (e p)) ≤ k
      rw [himg p]
      exact card_union_image_le_of_shared_edge_of_no_singleton_nonloop_edge p.1 p.2 hshare hns
    _ ≤ n ^ k * k ^ (2 * k) := by
      have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
        rw [Fintype.card_sum, Fintype.card_fin, two_mul]
      simpa [hcard] using card_filter_card_image_le (α := Fin k ⊕ Fin k) (β := Fin n) k

/-- **Variance bound for normalized Wigner traces.** When the entry array has jointly independent
coordinates, centered off-diagonal entries, and `2 * k`-th absolute moments bounded by `B`, the
variance of `n⁻¹ * Re tr(Hₙ ^ k)` is at most `2 * k ^ (2 * k) * B / n ^ 2` for all `k, n : ℕ`.
Neither diagonal centering nor any second-moment normalization is required. -/
theorem variance_inv_mul_re_trace_pow_wignerMatrix_le
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    {k : ℕ} {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) (n : ℕ) :
    Var[fun ω ↦ (n : ℝ)⁻¹ * ((wignerMatrix ξ η n ω ^ k).trace).re; P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n : ℝ) ^ 2 := by
  have := hindep.isProbabilityMeasure
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) (2 * k)).trans (hη 0)
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [pow_zero, trace_one, Fintype.card_fin]
    rw [ProbabilityTheory.variance_eq_integral aemeasurable_const]
    simp only [integral_const, probReal_univ, one_smul, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, smul_zero]
    positivity
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : (fun ω ↦ ((0 : ℕ) : ℝ)⁻¹ * ((wignerMatrix ξ η 0 ω ^ k).trace).re) = 0 := by
      ext ω; simp [_root_.inv_zero]
    rw [h0, ProbabilityTheory.variance_zero]
    simp
  rw [variance_re_trace_eq_re_sum_wordCov hk hξp hηp n]
  classical
  let Surv : Finset ((Fin k → Fin n) × (Fin k → Fin n)) := univ.filter IsSurvivingWordPair
  have hsum_eq :
      (∑ p : (Fin k → Fin n) × (Fin k → Fin n), wordCov ξ η P p.1 p.2) =
        ∑ p ∈ Surv, wordCov ξ η P p.1 p.2 :=
    (sum_subset (subset_univ Surv) fun p _ hp ↦ wordCov_eq_zero_of_not_surviving
      hindep hξzero hξp hηp fun h ↦ hp (mem_filter.mpr ⟨mem_univ _, h⟩)).symm
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsurv_card : (#Surv : ℝ) ≤ (n : ℝ) ^ k * (k : ℝ) ^ (2 * k) := by
    exact_mod_cast card_survivingWordPairs_le hn Surv fun p hp ↦ (mem_filter.mp hp).2
  rw [hsum_eq]
  calc (n : ℝ)⁻¹ ^ 2 * (∑ p ∈ Surv, wordCov ξ η P p.1 p.2).re
      ≤ (n : ℝ)⁻¹ ^ 2 * ∑ p ∈ Surv, ‖wordCov ξ η P p.1 p.2‖ :=
        mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (norm_sum_le _ _)) (by positivity)
    _ ≤ (n : ℝ)⁻¹ ^ 2 * ∑ _p ∈ Surv, (2 * (n : ℝ)⁻¹ ^ k * B) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun p _ ↦ norm_wordCov_le hk hξp hηp hξ hη p.1 p.2)
          (by positivity)
    _ ≤ (n : ℝ)⁻¹ ^ 2 * (((n : ℝ) ^ k * (k : ℝ) ^ (2 * k)) * (2 * (n : ℝ)⁻¹ ^ k * B)) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsurv_card (by positivity)) (by positivity)
    _ = 2 * (k : ℝ) ^ (2 * k) * B / (n : ℝ) ^ 2 := by simp only [inv_pow]; field_simp

end TraceVariance

namespace Probability

section Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- On a finite measure space, the `k`-th empirical spectral moment of `wignerMatrix` belongs to
`L²` whenever all coordinates belong to `L²ᵏ`. -/
theorem memLp_two_spectralMoment_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P := by
  simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin, RCLike.re_to_complex]
  exact memLp_two_inv_mul_re_trace_pow_wignerMatrix hξp hηp (n + 1)

/-- **Spectral-moment variance bound.** Under independent coordinates, centered off-diagonal
entries, and `2 * k`-th absolute moments bounded by `B`, the `k`-th empirical spectral moment has
variance at most `2 * k ^ (2 * k) * B / (n + 1) ^ 2`. -/
theorem variance_spectralMoment_wignerMatrix_le
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    {k : ℕ} {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) (n : ℕ) :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin, RCLike.re_to_complex]
  simpa [Nat.cast_add, Nat.cast_one] using
    variance_inv_mul_re_trace_pow_wignerMatrix_le hindep hξzero hξp hηp hξ hη (n + 1)

/-- **Chebyshev tail bound for empirical spectral moments.** -/
theorem measure_spectralMoment_wignerMatrix_sub_mean_ge
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    {k : ℕ} {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have := hindep.isProbabilityMeasure
  exact (meas_ge_le_variance_div_sq (memLp_two_spectralMoment_wignerMatrix hξp hηp n) hε).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (variance_spectralMoment_wignerMatrix_le hindep hξzero hξp hηp hξ hη n) (sq_nonneg ε)))

/-- Fluctuations of the `k`-th empirical spectral moment around its mean vanish in probability for
triangular Wigner arrays under a uniform `2 * k`-th moment bound. -/
theorem tendsto_spectralMoment_wignerMatrix_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n|})
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreal : Tendsto (fun n : ℕ ↦ (2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2)
      atTop (𝓝 0) := by
    convert ((hinv.pow 2).const_mul (2 * (k : ℝ) ^ (2 * k) * B)).div_const (ε ^ 2) using 1
    · ext n; simp [div_eq_mul_inv, inv_pow]
    · simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.tendsto_ofReal hreal) (fun _ ↦ bot_le)
    fun n ↦ measure_spectralMoment_wignerMatrix_sub_mean_ge
      (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n) n hε

/-- **Convergence in probability of empirical spectral moments** to the standard semicircle moments
for triangular Wigner arrays under a uniform `2 * k`-th moment bound. -/
theorem tendsto_spectralMoment_wignerMatrix_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
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
  have (n : ℕ) := (hindep n).isProbabilityMeasure
  rcases eq_or_ne k 0 with rfl | hk
  · refine tendsto_const_nhds.congr fun n ↦ ?_
    simp [not_le_of_gt hε]
  · have hξk := fun n ij ↦ memLp_and_integral_norm_pow_le_sqrt hk (hξp n ij) (hξ n ij)
    have hηk := fun n i ↦ memLp_and_integral_norm_pow_le_sqrt hk (hηp n i) (hη n i)
    have hmean := tendsto_integral_spectralMoment_wignerMatrix_array hindep hξzero hsecond
      (fun n ij ↦ (hξk n ij).1) (fun n i ↦ (hηk n i).1)
      (fun n ij ↦ (hξk n ij).2) (fun n i ↦ (hηk n i).2)
    have hfluc := tendsto_spectralMoment_wignerMatrix_sub_mean_probability
      hindep hξzero hξp hηp hξ hη (half_pos hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
      (Eventually.of_forall fun _ ↦ bot_le) ?_
    filter_upwards [Metric.tendsto_nhds.1 hmean (ε / 2) (half_pos hε)] with n hn
    refine measure_mono fun ω hω ↦ ?_
    rw [Real.dist_eq] at hn
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith [abs_sub_le
      (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      (∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n)
      (∫ x, x ^ k ∂semicircleReal 0 1)]

private theorem ae_tendsto_nhds_zero_of_measure_ge_le_div_sq {X : ℕ → Ω → ℝ} {C : ℝ}
    (h : ∀ (n : ℕ) {ε : ℝ}, 0 < ε →
      P {ω | ε ≤ |X n ω|} ≤ ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ε ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 0) := by
  have hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, inv_pow] using
      (summable_nat_add_iff 1).2 ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))
  have hbc (j : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |X n ω| < (j + 1 : ℝ)⁻¹ := by
    have hbound (n : ℕ) : P {ω | (j + 1 : ℝ)⁻¹ ≤ |X n ω|} ≤
        ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ((j + 1 : ℝ)⁻¹) ^ 2) :=
      h n (inv_pos.mpr (by positivity))
    have ht := Summable.mul_right ((((j + 1 : ℝ)⁻¹) ^ 2)⁻¹) (Summable.mul_left C hs)
    have hsum : Summable (fun n : ℕ ↦ (C / (n + 1 : ℝ) ^ 2) / ((j + 1 : ℝ)⁻¹) ^ 2) := by
      simpa only [div_eq_mul_inv, inv_pow, mul_assoc] using ht
    have hfinite : (∑' n, P {ω | (j + 1 : ℝ)⁻¹ ≤ |X n ω|}) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum hbound)
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfinite
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn.trans (by simpa only [one_div] using hj)

/-- Fluctuations of the `k`-th empirical spectral moment around its mean tend almost surely to zero
under a uniform `2 * k`-th moment bound. -/
theorem ae_tendsto_spectralMoment_wignerMatrix_sub_mean
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    {k : ℕ} {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) :=
  ae_tendsto_nhds_zero_of_measure_ge_le_div_sq fun n _ hε ↦
    measure_spectralMoment_wignerMatrix_sub_mean_ge hindep hξzero hξp hηp hξ hη n hε

/-- **Almost-sure convergence of empirical spectral moments.** Under independent coordinates,
centered unit-variance off-diagonal entries, and uniformly bounded `2 * k`-th absolute moments, the
`k`-th empirical spectral moment tends almost surely to the `k`-th standard semicircle moment. -/
theorem ae_tendsto_spectralMoment_wignerMatrix
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    {k : ℕ} {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have := hindep.isProbabilityMeasure
  rcases eq_or_ne k 0 with rfl | hk
  · refine ae_of_all P fun ω ↦ tendsto_const_nhds.congr fun n ↦ ?_
    simp
  · have hξk := fun ij ↦ memLp_and_integral_norm_pow_le_sqrt hk (hξp ij) (hξ ij)
    have hηk := fun i ↦ memLp_and_integral_norm_pow_le_sqrt hk (hηp i) (hη i)
    have hmean := tendsto_integral_spectralMoment_wignerMatrix hindep hξzero hsecond
      (fun ij ↦ (hξk ij).1) (fun i ↦ (hηk i).1) (fun ij ↦ (hξk ij).2) (fun i ↦ (hηk i).2)
    filter_upwards [ae_tendsto_spectralMoment_wignerMatrix_sub_mean hindep hξzero hξp hηp hξ hη]
      with ω hω
    simpa only [sub_add_cancel, zero_add] using hω.add hmean

private theorem integrable_pow_spectralMeasure {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) (A.spectralMeasure hA : Measure ℝ) := by
  rw [Matrix.spectralMeasure_def, empiricalMeasureOfFintype_toMeasure, integrable_finsetSum_measure]
  exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)

/-- **Wigner's semicircle law under bounded moments.** When the entry array has jointly independent
coordinates, centered unit-variance off-diagonal entries, and uniformly bounded positive even
moments, the empirical spectral measure of `wignerMatrix ξ η (n + 1) ω` converges weakly almost
surely to `semicircleReal 0 1`. Diagonal entries need not be centered or identically distributed. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ (k : ℕ) (ij : StrictUpper), k ≠ 0 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ (k i : ℕ), k ≠ 0 → MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ k : ℕ, k ≠ 0 → ∃ B : ℝ, ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ k : ℕ, k ≠ 0 → ∃ B : ℝ, ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)))
      atTop (𝓝 ⟨semicircleReal 0 1, inferInstance⟩) := by
  have := hindep.isProbabilityMeasure
  have hall : ∀ k : ℕ, ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := fun k ↦ by
    rcases eq_or_ne k 0 with rfl | hk
    · refine ae_of_all P fun ω ↦ tendsto_const_nhds.congr fun n ↦ ?_
      simp
    · obtain ⟨B₁, hB₁⟩ := hξ k hk
      obtain ⟨B₂, hB₂⟩ := hη k hk
      exact ae_tendsto_spectralMoment_wignerMatrix (B := max B₁ B₂) hindep hξzero hsecond
        (fun ij ↦ hξp k ij hk) (fun i ↦ hηp k i hk)
        (fun ij ↦ (hB₁ ij).trans (le_max_left _ _)) (fun i ↦ (hB₂ i).trans (le_max_right _ _))
  have hsupp : (semicircleReal 0 1) (Set.Icc (-2 : ℝ) 2)ᶜ = 0 := by
    have h := ae_mem_Icc_semicircleReal 0 1
    rw [NNReal.coe_one, Real.sqrt_one, mul_one, zero_sub, zero_add] at h
    exact ae_iff.mp h
  filter_upwards [ae_all_iff.2 hall] with ω hω
  exact ProbabilityMeasure.tendsto_of_tendsto_integral_pow isCompact_Icc hsupp
    (fun k ↦ Eventually.of_forall fun n ↦ integrable_pow_spectralMeasure _ _ k) hω

/-- Almost-sure convergence of integrals of bounded continuous test functions against the empirical
spectral measure of `wignerMatrix` under bounded positive even moments. -/
theorem ae_tendsto_integral_spectralMeasure_wignerMatrix
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ (k : ℕ) (ij : StrictUpper), k ≠ 0 → MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ (k i : ℕ), k ≠ 0 → MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ k : ℕ, k ≠ 0 → ∃ B : ℝ, ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ k : ℕ, k ≠ 0 → ∃ B : ℝ, ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n ↦
      ∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, f x ∂semicircleReal 0 1)) := by
  filter_upwards [ae_tendsto_spectralMeasure_wignerMatrix hindep hξzero hsecond hξp hηp hξ hη]
    with ω hω f
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hω) f

end Concentration

end Probability

end TauCeti
