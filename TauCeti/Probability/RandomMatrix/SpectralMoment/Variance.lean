/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Pair
public import TauCeti.Probability.RandomMatrix.SpectralMoment.Expectation
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Variance and concentration of Wigner spectral moments

For a normalized Wigner matrix `Hₙ = wignerMatrix ξ η n` whose coordinates are jointly independent
with centered strictly upper entries and `2k`th absolute moments bounded by `B`, the variance of the
real part of the unnormalized trace `tr(Hₙ^k)` is bounded by `2 * k^(2k) * B` uniformly in `n`.
After dividing by `n`, the `k`th empirical spectral moment has variance `O_k(n⁻²)`, yielding
Chebyshev tail bounds, convergence in probability to its expectation for triangular arrays, and
almost-sure vanishing of fluctuations via Borel-Cantelli for a single infinite array.

The proof expands `E[|tr(Hₙ^k) - E tr(Hₙ^k)|^2]` over pairs `(w₁, w₂)` of cyclic words of length
`k`:
* pairs with disjoint unordered edge sets have zero covariance by entry independence;
* pairs whose combined multiset of steps has a singleton nonloop unordered edge vanish in both
  `E[F(w₁) conj(F(w₂))]` and `E[F(w₁)] conj(E[F(w₂)])` under off-diagonal centering alone;
* at most `n^k * k^(2k)` pairs remain by
  `card_filter_pair_le_of_shared_edge_of_no_singleton_nonloop_edge`, and each contributes at most
  `2 * n⁻ᵏ * B` in norm.

No diagonal centering or identical-distribution assumption is needed, and `k = 0` is included.

## Main results

* `TauCeti.memLp_trace_pow_wignerMatrix` and
  `TauCeti.memLp_integral_pow_spectralMeasure_wignerMatrix`: `L²` integrability under `2k`th entry
  moments.
* `TauCeti.variance_re_trace_pow_wignerMatrix_le`: uniform `2 * k^(2k) * B` bound on the variance of
  `Re tr(Hₙ^k)`.
* `TauCeti.variance_integral_pow_spectralMeasure_wignerMatrix_le`: `2 * k^(2k) * B / (n + 1)^2`
  variance bound for the `k`th empirical spectral moment.
* `TauCeti.measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge`: Chebyshev tail bound for
  spectral moment fluctuations.
* `TauCeti.tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability`: spectral moment
  fluctuations vanish in probability for triangular Wigner arrays.
* `TauCeti.ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean`: spectral moment
  fluctuations vanish almost surely on a single infinite Wigner array.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.4, Lemma 2.1.7.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology ENNReal

namespace TauCeti

section FixedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

private theorem memLp_prod_wignerMatrix_apply_two {k : ℕ} (hk : k ≠ 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    {n : ℕ} (u v : Fin k → Fin n) :
    MemLp (fun ω ↦ ∏ t, wignerMatrix ξ η n ω (u t) (v t)) 2 P := by
  have h := MemLp.fun_prod (s := Finset.univ) (p := fun _ : Fin k ↦ ((2 * k : ℕ) : ℝ≥0∞))
    fun t _ ↦ memLp_wignerMatrix_apply hξp hηp (u t) (v t)
  have hexp : (∑ _t : Fin k, (((2 * k : ℕ) : ℝ≥0∞))⁻¹)⁻¹ = 2 := by
    have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
      Nat.cast_ofNat, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
      ← mul_assoc, mul_comm (k : ℝ≥0∞) 2⁻¹, mul_assoc,
      ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k), mul_one, inv_inv]
  rwa [hexp] at h

/-- When the Wigner array entries have finite `2k`th moments on a finite measure space, the trace
of `wignerMatrix ξ η n ω ^ k` lies in `L²(P)`. -/
theorem memLp_trace_pow_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) 2 P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [memLp_const]
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    exact memLp_finsetSum Finset.univ fun w _ ↦
      memLp_prod_wignerMatrix_apply_two hk hξp hηp _ _

/-- When the Wigner array entries have finite `2k`th moments on a finite measure space, the `k`th
empirical spectral moment of `wignerMatrix ξ η (n + 1)` lies in `L²(P)`. -/
theorem memLp_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P := by
  have hre : MemLp (fun ω ↦ ((wignerMatrix ξ η (n + 1) ω ^ k).trace).re) 2 P :=
    Complex.reCLM.comp_memLp' (memLp_trace_pow_wignerMatrix hξp hηp (n + 1))
  have hpt : (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      fun ω ↦ (((n + 1 : ℕ) : ℝ)⁻¹ * ((wignerMatrix ξ η (n + 1) ω ^ k).trace).re) := by
    ext ω
    simp [Matrix.integral_pow_spectralMeasure]
  rw [hpt]
  exact hre.const_mul _

private theorem variance_re_le_norm_integral_mul_star_sub [IsProbabilityMeasure P]
    {Z : Ω → ℂ} (hZ : MemLp Z 2 P) :
    Var[fun ω ↦ (Z ω).re; P] ≤
      ‖(∫ ω, Z ω * star (Z ω) ∂P) - (∫ ω, Z ω ∂P) * star (∫ ω, Z ω ∂P)‖ := by
  have hZre : MemLp (fun ω ↦ (Z ω).re) 2 P := Complex.reCLM.comp_memLp' hZ
  have hZint : Integrable Z P := hZ.integrable one_le_two
  have hre_int : ∫ ω, (Z ω).re ∂P = (∫ ω, Z ω ∂P).re := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hZint
  set μ : ℂ := ∫ ω, Z ω ∂P
  have hsub : MemLp (fun ω ↦ Z ω - μ) 2 P := hZ.sub (memLp_const μ)
  have hvar_le : Var[fun ω ↦ (Z ω).re; P] ≤ ∫ ω, ‖Z ω - μ‖ ^ 2 ∂P := by
    rw [variance_eq_integral hZre.aemeasurable]
    refine integral_mono (hZre.sub (memLp_const _)).integrable_sq
      (hsub.integrable_norm_pow (by simp)) fun ω ↦ ?_
    rw [hre_int, ← Complex.sub_re]
    exact sq_le_sq.mpr (by simpa only [abs_norm] using Complex.abs_re_le_norm (Z ω - μ))
  have hr_nonneg : 0 ≤ ∫ ω, ‖Z ω - μ‖ ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  have hident : ((∫ ω, ‖Z ω - μ‖ ^ 2 ∂P : ℝ) : ℂ) =
      (∫ ω, Z ω * star (Z ω) ∂P) - μ * star μ := by
    rw [← integral_complex_ofReal]
    have hpt (ω : Ω) : ((‖Z ω - μ‖ ^ 2 : ℝ) : ℂ) =
        Z ω * star (Z ω) - Z ω * star μ - μ * star (Z ω) + μ * star μ := by
      rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, star_sub]
      ring
    simp_rw [hpt]
    have hi1 : Integrable (fun ω ↦ Z ω * star (Z ω)) P := hZ.integrable_mul hZ.star
    have hi2 : Integrable (fun ω ↦ Z ω * star μ) P := hZint.mul_const _
    have hi3 : Integrable (fun ω ↦ μ * star (Z ω)) P :=
      (hZ.star.integrable one_le_two).const_mul _
    rw [integral_add, integral_sub, integral_sub]
    · rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ, one_smul]
      simp only [Complex.star_def, integral_conj]; ring
    exacts [hi1, hi2, hi1.sub hi2, hi3, (hi1.sub hi2).sub hi3, integrable_const _]
  refine hvar_le.trans ?_
  have hnorm : ∫ ω, ‖Z ω - μ‖ ^ 2 ∂P = ‖((∫ ω, ‖Z ω - μ‖ ^ 2 ∂P : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr_nonneg]
  rw [hnorm, hident]

omit [MeasurableSpace Ω] in
private theorem star_prod_wignerMatrix_eq {k n : ℕ} (ω : Ω) (w : Fin k → Fin n) :
    star (∏ j, wignerMatrix ξ η n ω (w j) (w (finRotate k j))) =
      ∏ j, wignerMatrix ξ η n ω (w (finRotate k j)) (w j) := by
  rw [star_prod]
  exact Finset.prod_congr rfl fun j _ ↦
    (wignerMatrix_isHermitian ξ η ω n).apply (w (finRotate k j)) (w j)

omit [MeasurableSpace Ω] in
private theorem prod_wignerMatrix_mul_star_eq {k n : ℕ} (ω : Ω) (w₁ w₂ : Fin k → Fin n) :
    (∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k i))) *
        star (∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k j))) =
      ∏ t : Fin k ⊕ Fin k, wignerMatrix ξ η n ω
        (Sum.elim w₁ (fun j ↦ w₂ (finRotate k j)) t)
        (Sum.elim (fun i ↦ w₁ (finRotate k i)) w₂ t) := by
  rw [star_prod_wignerMatrix_eq, Fintype.prod_sum_type]
  rfl

private theorem edge_sumElim_eq {k n : ℕ} (w₁ w₂ : Fin k → Fin n) (t : Fin k ⊕ Fin k) :
    s(Sum.elim w₁ (fun j ↦ w₂ (finRotate k j)) t,
        Sum.elim (fun i ↦ w₁ (finRotate k i)) w₂ t) =
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k j))) t := by
  rcases t with i | j <;> simp [Sym2.eq_swap]

private noncomputable abbrev wordProd (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    {k n : ℕ} (w : Fin k → Fin n) (ω : Ω) : ℂ :=
  ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate k t))

private noncomputable abbrev wordPairCov (P : Measure Ω)
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) {k n : ℕ} (w₁ w₂ : Fin k → Fin n) : ℂ :=
  (∫ ω, wordProd ξ η w₁ ω * star (wordProd ξ η w₂ ω) ∂P) -
    (∫ ω, wordProd ξ η w₁ ω ∂P) * star (∫ ω, wordProd ξ η w₂ ω ∂P)

private abbrev ConnectedWordPair {k n : ℕ} (p : (Fin k → Fin n) × (Fin k → Fin n)) : Prop :=
  (∃ i j : Fin k, s(p.1 i, p.1 (finRotate k i)) = s(p.2 j, p.2 (finRotate k j))) ∧
    ∀ t : Fin k ⊕ Fin k,
      ¬(Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k i)))
          (fun i ↦ s(p.2 i, p.2 (finRotate k i))) t).IsDiag →
        ∃ s ≠ t,
          Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k i)))
            (fun i ↦ s(p.2 i, p.2 (finRotate k i))) s =
          Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k i)))
            (fun i ↦ s(p.2 i, p.2 (finRotate k i))) t

private theorem integral_prod_mul_star_sub_eq_zero_of_disjoint {k n : ℕ} (hk : k ≠ 0)
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (w₁ w₂ : Fin k → Fin n)
    (hdisj : ¬∃ i j : Fin k, s(w₁ i, w₁ (finRotate k i)) = s(w₂ j, w₂ (finRotate k j))) :
    wordPairCov P ξ η w₁ w₂ = 0 := by
  push Not at hdisj
  have hind := indepFun_prod_wignerMatrix_apply_of_edge_ne
    (fun ij ↦ (hξp ij).aestronglyMeasurable.aemeasurable)
    (fun i ↦ (hηp i).aestronglyMeasurable.aemeasurable) hindep
    w₁ (fun i ↦ w₁ (finRotate k i)) (fun j ↦ w₂ (finRotate k j)) w₂
    fun i j ↦ by simpa only [Sym2.eq_swap (a := w₂ (finRotate k j))] using hdisj i j
  have h1 := (memLp_prod_wignerMatrix_apply_two hk hξp hηp w₁
    (fun i ↦ w₁ (finRotate k i))).aestronglyMeasurable
  have h2 := (memLp_prod_wignerMatrix_apply_two hk hξp hηp (fun j ↦ w₂ (finRotate k j))
    w₂).aestronglyMeasurable
  dsimp only [wordPairCov, wordProd]
  simp_rw [star_prod_wignerMatrix_eq]
  rw [hind.integral_fun_mul_eq_mul_integral h1 h2]
  simp_rw [← star_prod_wignerMatrix_eq, Complex.star_def, integral_conj, sub_self]

private theorem integral_prod_mul_star_sub_eq_zero_of_singleton_nonloop {k n : ℕ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (w₁ w₂ : Fin k → Fin n)
    (hsing : ¬∀ t : Fin k ⊕ Fin k,
      ¬(Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k j))) t).IsDiag →
        ∃ s ≠ t,
          Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k i)))
            (fun j ↦ s(w₂ j, w₂ (finRotate k j))) s =
          Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k i)))
            (fun j ↦ s(w₂ j, w₂ (finRotate k j))) t) :
    wordPairCov P ξ η w₁ w₂ = 0 := by
  push Not at hsing
  obtain ⟨t, hnd, huniq⟩ := hsing
  dsimp only [wordPairCov, wordProd]
  have hprod : ∫ ω, (∏ i, wignerMatrix ξ η n ω (w₁ i) (w₁ (finRotate k i))) *
      star (∏ j, wignerMatrix ξ η n ω (w₂ j) (w₂ (finRotate k j))) ∂P = 0 := by
    simp_rw [prod_wignerMatrix_mul_star_eq]
    refine integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero _ _ (t := t)
      ?_ fun s hs ↦ ?_
    · intro heq
      exact hnd (by rw [← edge_sumElim_eq, Sym2.mk_isDiag_iff]; exact heq)
    · rw [edge_sumElim_eq, edge_sumElim_eq] at hs
      exact by_contra fun hst ↦ huniq s hst hs
  rw [hprod, zero_sub, neg_eq_zero]
  rcases t with i | j
  · have hw₁ : ∫ ω, ∏ i', wignerMatrix ξ η n ω (w₁ i') (w₁ (finRotate k i')) ∂P = 0 :=
      integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero _ _ (t := i)
        (by simpa only [Sum.elim_inl, Sym2.mk_isDiag_iff] using hnd)
        fun i' hi' ↦ by_contra fun hne ↦ huniq (Sum.inl i') (Sum.inl_injective.ne hne) hi'
    rw [hw₁, zero_mul]
  · have hw₂ : ∫ ω, ∏ j', wignerMatrix ξ η n ω (w₂ j') (w₂ (finRotate k j')) ∂P = 0 :=
      integral_prod_wignerMatrix_apply_eq_zero_of_ne hξm hηm hindep hξzero _ _ (t := j)
        (by simpa only [Sum.elim_inr, Sym2.mk_isDiag_iff] using hnd)
        fun j' hj' ↦ by_contra fun hne ↦ huniq (Sum.inr j') (Sum.inr_injective.ne hne) hj'
    rw [hw₂, star_zero, mul_zero]

private theorem norm_integral_prod_mul_star_sub_le [IsProbabilityMeasure P] {k n : ℕ}
    (hk : k ≠ 0) {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w₁ w₂ : Fin k → Fin n) :
    ‖wordPairCov P ξ η w₁ w₂‖ ≤ 2 * ((Real.sqrt n)⁻¹ ^ (2 * k) * B) := by
  set M : ℝ := (Real.sqrt n)⁻¹ ^ (2 * k) * B
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0)
  have hM : 0 ≤ M := mul_nonneg (by positivity) hB
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  have hpair (u₁ u₂ : Fin k → Fin n) :
      ‖∫ ω, wordProd ξ η u₁ ω * star (wordProd ξ η u₂ ω) ∂P‖ ≤ M := by
    simp_rw [wordProd, prod_wignerMatrix_mul_star_eq]
    simpa only [hcard, M] using
      norm_integral_prod_wignerMatrix_apply_le (ι := Fin k ⊕ Fin k)
        (by simpa only [hcard] using hξp) (by simpa only [hcard] using hηp)
        (by simpa only [hcard] using hξ) (by simpa only [hcard] using hη) _ _
  have hsingle (w : Fin k → Fin n) : ‖∫ ω, wordProd ξ η w ω ∂P‖ ≤ Real.sqrt M := by
    have hFw : MemLp (wordProd ξ η w) 2 P := memLp_prod_wignerMatrix_apply_two hk hξp hηp _ _
    have hvar := variance_nonneg (fun ω ↦ ‖wordProd ξ η w ω‖) P
    rw [variance_eq_sub hFw.norm] at hvar
    have hsq : ‖∫ ω, wordProd ξ η w ω ∂P‖ ^ 2 ≤ ∫ ω, ‖wordProd ξ η w ω‖ ^ 2 ∂P :=
      (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans (by
        simpa only [Pi.pow_apply, sub_nonneg] using hvar)
    have hl2 : ∫ ω, ‖wordProd ξ η w ω‖ ^ 2 ∂P ≤ M := by
      have hnn : 0 ≤ ∫ ω, ‖wordProd ξ η w ω‖ ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
      have heq : ((∫ ω, ‖wordProd ξ η w ω‖ ^ 2 ∂P : ℝ) : ℂ) =
          ∫ ω, wordProd ξ η w ω * star (wordProd ξ η w ω) ∂P := by
        rw [← integral_complex_ofReal]
        congr with ω
        rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
      rw [← Real.norm_of_nonneg hnn, ← Complex.norm_real, heq]
      exact hpair w w
    exact Real.le_sqrt_of_sq_le (hsq.trans hl2)
  have hmul : ‖(∫ ω, wordProd ξ η w₁ ω ∂P) * star (∫ ω, wordProd ξ η w₂ ω ∂P)‖ ≤ M := by
    rw [norm_mul, norm_star]
    exact (mul_le_mul (hsingle w₁) (hsingle w₂) (norm_nonneg _) (Real.sqrt_nonneg M)).trans_eq
      (Real.mul_self_sqrt hM)
  exact (norm_sub_le _ _).trans (by linarith [hpair w₁ w₂])

private theorem trace_pow_mul_star_sub_eq_sum [IsFiniteMeasure P] {k n : ℕ} (hk : k ≠ 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) :
    (∫ ω, (wignerMatrix ξ η n ω ^ k).trace * star (wignerMatrix ξ η n ω ^ k).trace ∂P) -
      (∫ ω, (wignerMatrix ξ η n ω ^ k).trace ∂P) *
        star (∫ ω, (wignerMatrix ξ η n ω ^ k).trace ∂P) =
      ∑ p : (Fin k → Fin n) × (Fin k → Fin n), wordPairCov P ξ η p.1 p.2 := by
  let F (w : Fin k → Fin n) := wordProd ξ η w
  have hFw (w : Fin k → Fin n) : MemLp (F w) 2 P := memLp_prod_wignerMatrix_apply_two hk hξp hηp _ _
  simp_rw [trace_pow_eq_sum_prod _ hk]
  have h1 : (∫ ω, (∑ w₁, F w₁ ω) * star (∑ w₂, F w₂ ω) ∂P) =
      ∑ p : (Fin k → Fin n) × (Fin k → Fin n), ∫ ω, F p.1 ω * star (F p.2 ω) ∂P := by
    simp_rw [star_sum, sum_mul_sum, ← Fintype.sum_prod_type']
    exact integral_finsetSum _ fun p _ ↦ (hFw p.1).integrable_mul (hFw p.2).star
  have h2 : (∫ ω, ∑ w₁, F w₁ ω ∂P) * star (∫ ω, ∑ w₂, F w₂ ω ∂P) =
      ∑ p : (Fin k → Fin n) × (Fin k → Fin n), (∫ ω, F p.1 ω ∂P) * star (∫ ω, F p.2 ω ∂P) := by
    rw [integral_finsetSum _ fun w _ ↦ (hFw w).integrable one_le_two, star_sum,
      sum_mul_sum, ← Fintype.sum_prod_type']
  exact (congrArg₂ (· - ·) h1 h2).trans (sum_sub_distrib _ _).symm

private theorem trace_pow_mul_star_sub_eq_sum_filter {k n : ℕ} (hk : k ≠ 0)
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) :
    (∫ ω, (wignerMatrix ξ η n ω ^ k).trace * star (wignerMatrix ξ η n ω ^ k).trace ∂P) -
      (∫ ω, (wignerMatrix ξ η n ω ^ k).trace ∂P) *
        star (∫ ω, (wignerMatrix ξ η n ω ^ k).trace ∂P) =
      ∑ p : (Fin k → Fin n) × (Fin k → Fin n) with ConnectedWordPair p,
        wordPairCov P ξ η p.1 p.2 := by
  have := hindep.isProbabilityMeasure
  rw [trace_pow_mul_star_sub_eq_sum hk hξp hηp]
  refine (sum_filter_of_ne fun p _ hp ↦ ?_).symm
  by_cases hsh : ∃ i j : Fin k, s(p.1 i, p.1 (finRotate k i)) = s(p.2 j, p.2 (finRotate k j))
  · refine ⟨hsh, by_contra fun hns ↦ hp ?_⟩
    exact integral_prod_mul_star_sub_eq_zero_of_singleton_nonloop hindep hξzero
      (fun ij ↦ (hξp ij).aestronglyMeasurable.aemeasurable)
      (fun i ↦ (hηp i).aestronglyMeasurable.aemeasurable) p.1 p.2 hns
  · exact False.elim (hp (integral_prod_mul_star_sub_eq_zero_of_disjoint hk hindep hξp hηp
      p.1 p.2 hsh))

/-- **Uniform variance bound for unnormalized Wigner traces.** When the array coordinates are
jointly independent, the strictly upper entries have mean zero, and all `2k`th absolute moments are
bounded by `B`, the variance of `Re tr(Hₙ^k)` is at most `2 * k^(2k) * B` for all `k, n : ℕ`. -/
theorem variance_re_trace_pow_wignerMatrix_le {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) (n : ℕ) :
    Var[fun ω ↦ ((wignerMatrix ξ η n ω ^ k).trace).re; P] ≤
      2 * (k : ℝ) ^ (2 * k) * B := by
  classical
  have := hindep.isProbabilityMeasure
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0)
  rcases eq_or_ne k 0 with rfl | hk
  · have hconst : (fun ω ↦ ((wignerMatrix ξ η n ω ^ 0).trace).re) = fun _ ↦ (n : ℝ) := by
      ext ω; simp
    rw [hconst, variance_eq_integral aemeasurable_const]
    simpa using mul_nonneg zero_le_two hB
  rcases eq_or_ne n 0 with rfl | hn
  · have hzero : (fun ω ↦ ((wignerMatrix ξ η 0 ω ^ k).trace).re) = 0 := by ext ω; simp
    rw [hzero, variance_zero]; positivity
  let S : Finset ((Fin k → Fin n) × (Fin k → Fin n)) := {p | ConnectedWordPair p}
  have hcardS : #S ≤ n ^ k * k ^ (2 * k) := by
    simpa [S, ConnectedWordPair, Fintype.card_fin] using
      card_filter_pair_le_of_shared_edge_of_no_singleton_nonloop_edge (α := Fin n) k
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsqrt : (Real.sqrt n)⁻¹ ^ (2 * k) = ((n : ℝ) ^ k)⁻¹ := by
    rw [pow_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), inv_pow]
  refine (variance_re_le_norm_integral_mul_star_sub (memLp_trace_pow_wignerMatrix hξp hηp n)).trans
    ?_
  rw [trace_pow_mul_star_sub_eq_sum_filter hk hindep hξzero hξp hηp]
  calc
    ‖∑ p ∈ S, wordPairCov P ξ η p.1 p.2‖ ≤ ∑ p ∈ S, ‖wordPairCov P ξ η p.1 p.2‖ := norm_sum_le S _
    _ ≤ ∑ _p ∈ S, 2 * ((Real.sqrt n)⁻¹ ^ (2 * k) * B) :=
      sum_le_sum fun p _ ↦ norm_integral_prod_mul_star_sub_le hk hξp hηp hξ hη p.1 p.2
    _ = (#S : ℝ) * (2 * ((Real.sqrt n)⁻¹ ^ (2 * k) * B)) := by simp
    _ ≤ (n ^ k * k ^ (2 * k) : ℕ) * (2 * ((Real.sqrt n)⁻¹ ^ (2 * k) * B)) := by gcongr
    _ = 2 * (k : ℝ) ^ (2 * k) * B := by rw [hsqrt]; push_cast; field_simp

/-- **`O_k(n⁻²)` variance bound for empirical Wigner spectral moments.** Under coordinate
independence, off-diagonal centering, and a uniform `2k`th moment bound `B`, the variance of the
`k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)` is at most
`2 * k^(2k) * B / (n + 1)^2` for all `k, n : ℕ`. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) (n : ℕ) :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  have hpt : (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      fun ω ↦ (n + 1 : ℝ)⁻¹ * ((wignerMatrix ξ η (n + 1) ω ^ k).trace).re := by
    ext ω
    simp [Matrix.integral_pow_spectralMeasure]
  rw [hpt, variance_const_mul]
  calc
    (n + 1 : ℝ)⁻¹ ^ 2 * Var[fun ω ↦ ((wignerMatrix ξ η (n + 1) ω ^ k).trace).re; P] ≤
        (n + 1 : ℝ)⁻¹ ^ 2 * (2 * (k : ℝ) ^ (2 * k) * B) :=
      mul_le_mul_of_nonneg_left
        (variance_re_trace_pow_wignerMatrix_le hindep hξzero hξp hηp hξ hη (n + 1))
        (sq_nonneg _)
    _ = 2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
      rw [inv_pow, div_eq_mul_inv]
      ring

/-- **Chebyshev tail bound for empirical Wigner spectral moments.** Under coordinate independence,
off-diagonal centering, and `2k`th moment bound `B`, the deviation of the `k`th empirical spectral
moment from its mean has `O_k((n + 1)⁻² ε⁻²)` tail probability. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have := hindep.isProbabilityMeasure
  refine (meas_ge_le_variance_div_sq
    (memLp_integral_pow_spectralMeasure_wignerMatrix hξp hηp n) hε).trans ?_
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (variance_integral_pow_spectralMeasure_wignerMatrix_le hindep hξzero hξp hηp hξ hη n)
    (sq_nonneg ε))

private theorem ae_tendsto_zero_of_measure_ge_le {X : ℕ → Ω → ℝ} {C : ℝ}
    (hbound : ∀ n {ε : ℝ}, 0 < ε →
      P {ω | ε ≤ |X n ω|} ≤ ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ε ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 0) := by
  have hs : Summable (fun n : ℕ ↦ ((n + 1 : ℝ) ^ 2)⁻¹) :=
    ((summable_nat_add_iff 1).2
      ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))).congr fun n ↦ by
        push_cast; rfl
  have hbc (m : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |X n ω| < (m + 1 : ℝ)⁻¹ := by
    have hm (n : ℕ) : P {ω | (m + 1 : ℝ)⁻¹ ≤ |X n ω|} ≤
        ENNReal.ofReal ((C / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) :=
      hbound n (inv_pos.mpr (by positivity))
    have hsum : Summable (fun n : ℕ ↦ (C / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) :=
      ((hs.mul_left C).div_const (((m + 1 : ℝ)⁻¹) ^ 2)).congr fun n ↦ by
        simp only [div_eq_mul_inv]
    have hfinite : (∑' n, P {ω | (m + 1 : ℝ)⁻¹ ≤ |X n ω|}) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum hm)
    exact (ae_eventually_notMem hfinite).mono fun ω hω ↦
      hω.mono fun n hn ↦ not_le.mp hn
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω m] with n hn
  rw [Real.dist_eq, sub_zero]
  exact hn.trans (by rwa [one_div] at hm)

/-- **Borel-Cantelli almost-sure vanishing of spectral moment fluctuations.** On a single infinite
Wigner array with independent coordinates, centered strictly upper entries, and `2k`th moments
bounded by `B`, the `k`th empirical spectral moment minus its expectation tends to zero almost
surely as `n → ∞`. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) :=
  ae_tendsto_zero_of_measure_ge_le fun n _ hε ↦
    measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
      hindep hξzero hξp hηp hξ hη n hε

end FixedSpace

section TriangularArray

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
  {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}

/-- **Spectral moment fluctuations vanish in probability for triangular Wigner arrays.** Under
row-wise coordinate independence, off-diagonal centering, and uniformly bounded `2k`th moments, the
`k`th empirical spectral moment minus its expectation tends to zero in probability. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability {k : ℕ} {B : ℝ}
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
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hreal : Tendsto (fun n : ℕ ↦
      (2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) atTop (𝓝 0) := by
    convert ((hinv.pow 2).const_mul (2 * (k : ℝ) ^ (2 * k) * B)).div_const (ε ^ 2) using 1
    · ext n; simp [div_eq_mul_inv, inv_pow]
    · simp
  have hbound : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ bot_le) fun n ↦
      measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
        (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n) n hε

end TriangularArray

end TauCeti
