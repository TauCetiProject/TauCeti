/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Combinatorics.TraceWord.Pair
public import TauCeti.Probability.RandomMatrix.MomentBounds

/-!
# Variance bounds for spectral moments of Wigner matrices

Expanding the centered second moment of `(n : ℂ)⁻¹ * tr(Hₙᵏ)` expresses it as a sum of covariances
of length-`k` cyclic walk products `(P_{w₁}, P_{w₂})`. Two reductions eliminate the bulk of pairs:

* if `w₁` and `w₂` share no unordered edge, `P_{w₁}` and `star ∘ P_{w₂}` depend on disjoint sets of
  independent coordinates (`TauCeti.indepFun_prod_wignerMatrix_apply_of_ne`), so their covariance
  vanishes;
* if the combined `2 * k` steps of `(w₁, w₂)` contain a singleton unordered edge, both
  `E[P_{w₁} * star P_{w₂}]` and `E[P_{w₁}] * star E[P_{w₂}]` vanish by
  `TauCeti.integral_prod_wignerMatrix_apply_eq_zero`.

Every remaining pair shares an unordered edge and has no combined singleton edge, so by
`TauCeti.card_filter_shared_edge_and_no_singleton_edge_le` at most `n ^ k * k ^ (2 * k)` pairs
survive. Under a uniform `2 * k`-th moment bound `B`, each surviving covariance has norm at most
`2 * n⁻ᵏ * B`, giving a centered second-moment bound of `2 * k ^ (2 * k) * B / n ^ 2` for every
`k, n : ℕ`, hence a summable `O_k(n⁻²)` variance bound for the `k`-th empirical spectral moment.

## Main results

* `TauCeti.Probability.memLp_prod_wignerMatrix_apply_two`,
  `TauCeti.Probability.memLp_trace_pow_wignerMatrix_two`, and
  `TauCeti.Probability.memLp_integral_pow_spectralMeasure_wignerMatrix_two`: `L²` integrability of
  walk products, matrix traces, and empirical spectral moments from `L^(2k)` entry bounds.
* `TauCeti.Probability.integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le`: the `O_k(n⁻²)`
  centered second-moment bound for normalized traces `(n : ℂ)⁻¹ * tr(Hₙᵏ)`.
* `TauCeti.Probability.variance_integral_pow_spectralMeasure_wignerMatrix_le`: the `O_k((n + 1)⁻²)`
  variance bound for `∫ x, x ^ k ∂L_{Hₙ₊₁}`.
* `TauCeti.Probability.measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge` and
  `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability`:
  Chebyshev tail bound and convergence to the mean in probability for triangular arrays.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open TauCeti
open scoped Topology ENNReal

namespace TauCeti.Probability

section L2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- A product of `k = Fintype.card ι` Wigner entries lies in `L²` when the array entries lie in
`L^(2k)`. -/
theorem memLp_prod_wignerMatrix_apply_two {ι : Type*} [Fintype ι]
    (hξ : ∀ ij, MemLp (ξ ij) (2 * Fintype.card ι : ℕ) P)
    (hη : ∀ i, MemLp (η i) (2 * Fintype.card ι : ℕ) P) {n : ℕ} (u v : ι → Fin n) :
    MemLp (fun ω ↦ ∏ s, wignerMatrix ξ η n ω (u s) (v s)) 2 P := by
  cases isEmpty_or_nonempty ι
  · simp [memLp_const]
  have hc0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hct : (Fintype.card ι : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have h := MemLp.fun_prod (s := Finset.univ)
    (p := fun _ : ι ↦ ((2 * Fintype.card ι : ℕ) : ℝ≥0∞))
    fun s _ ↦ memLp_wignerMatrix_apply hξ hη (u s) (v s)
  have hexp : (∑ _s : ι, (((2 * Fintype.card ι : ℕ) : ℝ≥0∞))⁻¹)⁻¹ = 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl (by norm_num)), ← mul_assoc,
      mul_comm (Fintype.card ι : ℝ≥0∞) (2 : ℝ≥0∞)⁻¹, mul_assoc,
      ENNReal.mul_inv_cancel hc0 hct, mul_one, inv_inv]
  rwa [hexp] at h

/-- When the entries of the Wigner array lie in `L^(2k)`, the trace `(Hₙ ^ k).trace` lies in `L²`.
-/
theorem memLp_trace_pow_wignerMatrix_two {k : ℕ}
    (hξ : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hη : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) 2 P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [memLp_const]
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    have hξ' : ∀ ij, MemLp (ξ ij) (2 * Fintype.card (Fin k) : ℕ) P := by simpa using hξ
    have hη' : ∀ i, MemLp (η i) (2 * Fintype.card (Fin k) : ℕ) P := by simpa using hη
    exact memLp_finsetSum Finset.univ fun w _ ↦
      memLp_prod_wignerMatrix_apply_two hξ' hη' w fun t ↦ w (finRotate k t)

/-- When the entries of the Wigner array lie in `L^(2k)`, the `k`-th empirical spectral moment of
`Hₙ₊₁` lies in `L²`. -/
theorem memLp_integral_pow_spectralMeasure_wignerMatrix_two {k : ℕ}
    (hξ : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hη : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P := by
  simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin]
  exact (memLp_trace_pow_wignerMatrix_two hξ hη (n + 1)).re.const_mul _

end L2

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

private noncomputable abbrev walkProd {k n : ℕ} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (w : Fin k → Fin n) (ω : Ω) : ℂ :=
  ∏ t : Fin k, wignerMatrix ξ η n ω (w t) (w (finRotate k t))

private noncomputable def walkCov {k n : ℕ} (P : Measure Ω) (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (w₁ w₂ : Fin k → Fin n) : ℂ :=
  (∫ ω, walkProd ξ η w₁ ω * star (walkProd ξ η w₂ ω) ∂P) -
    (∫ ω, walkProd ξ η w₁ ω ∂P) * star (∫ ω, walkProd ξ η w₂ ω ∂P)

omit [MeasurableSpace Ω] in
private theorem walkProd_mul_star_eq_prod_sum {k n : ℕ} (w₁ w₂ : Fin k → Fin n) (ω : Ω) :
    walkProd ξ η w₁ ω * star (walkProd ξ η w₂ ω) =
      ∏ s : Fin k ⊕ Fin k, wignerMatrix ξ η n ω
        (Sum.elim w₁ (fun t ↦ w₂ (finRotate k t)) s)
        (Sum.elim (fun t ↦ w₁ (finRotate k t)) w₂ s) := by
  rw [Fintype.prod_sum_type, star_prod]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  refine prod_congr rfl fun t _ ↦ ?_
  simpa using (wignerMatrix_isHermitian ξ η ω n).apply (w₂ (finRotate k t)) (w₂ t)

private theorem sym2_pair_sum_eq {k n : ℕ} (w₁ w₂ : Fin k → Fin n) (s : Fin k ⊕ Fin k) :
    s(Sum.elim w₁ (fun t ↦ w₂ (finRotate k t)) s,
      Sum.elim (fun t ↦ w₁ (finRotate k t)) w₂ s) =
    Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
      (fun t ↦ s(w₂ t, w₂ (finRotate k t))) s := by
  cases s <;> simp [Sym2.eq_swap]

private theorem walkCov_eq_zero_of_disjoint_edges {k n : ℕ} {w₁ w₂ : Fin k → Fin n}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hP₁ : AEStronglyMeasurable (walkProd ξ η w₁) P)
    (hP₂ : AEStronglyMeasurable (walkProd ξ η w₂) P)
    (hdisj : ¬ ∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂))) :
    walkCov P ξ η w₁ w₂ = 0 := by
  push Not at hdisj
  have hind := (indepFun_prod_wignerMatrix_apply_of_ne hξm hηm hindep
    w₁ (w₁ ∘ finRotate k) w₂ (w₂ ∘ finRotate k) hdisj).comp
    measurable_id continuous_star.measurable
  have hmul := hind.integral_fun_mul_eq_mul_integral hP₁ hP₂.star
  simp only [Function.comp_apply, id_eq] at hmul
  rw [walkCov, hmul]
  simp only [Complex.star_def]
  rw [integral_conj, sub_self]

private theorem walkCov_eq_zero_of_singleton_edge {k n : ℕ}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (w₁ w₂ : Fin k → Fin n)
    (hsing : ¬ ∀ s : Fin k ⊕ Fin k, ∃ s' ≠ s,
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k t))) s' =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k t))) s) :
    walkCov P ξ η w₁ w₂ = 0 := by
  push Not at hsing
  obtain ⟨s₀, hs₀⟩ := hsing
  have hcomb : ∫ ω, walkProd ξ η w₁ ω * star (walkProd ξ η w₂ ω) ∂P = 0 := by
    simp_rw [walkProd_mul_star_eq_prod_sum]
    refine integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero _ _
      (t := s₀) fun s hs ↦ ?_
    rw [sym2_pair_sum_eq, sym2_pair_sum_eq] at hs
    exact by_contra fun hne ↦ hs₀ s hne hs
  have hprod : (∫ ω, walkProd ξ η w₁ ω ∂P) * star (∫ ω, walkProd ξ η w₂ ω ∂P) = 0 := by
    rcases s₀ with t₁ | t₂
    · have h₁ : ∫ ω, walkProd ξ η w₁ ω ∂P = 0 :=
        integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero _ _
          (t := t₁) fun s hs ↦ by_contra fun hne ↦
            hs₀ (.inl s) (by simp [hne]) (by simpa using hs)
      simp [h₁]
    · have h₂ : ∫ ω, walkProd ξ η w₂ ω ∂P = 0 :=
        integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero _ _
          (t := t₂) fun s hs ↦ by_contra fun hne ↦
            hs₀ (.inr s) (by simp [hne]) (by simpa using hs)
      simp [h₂]
  rw [walkCov, hcomb, hprod, sub_zero]

private theorem norm_integral_walkProd_mul_star_le {k n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (v₁ v₂ : Fin k → Fin n) :
    ‖∫ ω, walkProd ξ η v₁ ω * star (walkProd ξ η v₂ ω) ∂P‖ ≤ (n : ℝ)⁻¹ ^ k * B := by
  have hsqrt : (Real.sqrt n)⁻¹ ^ (2 * k) = (n : ℝ)⁻¹ ^ k := by
    rw [inv_pow, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n), inv_pow]
  simp_rw [walkProd_mul_star_eq_prod_sum]
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by simp [Nat.two_mul]
  simpa only [hcard, hsqrt] using norm_integral_prod_wignerMatrix_apply_le
    (by simpa [hcard] using hξp) (by simpa [hcard] using hηp)
    (by simpa [hcard] using hξ) (by simpa [hcard] using hη)
    (Sum.elim v₁ fun t ↦ v₂ (finRotate k t)) (Sum.elim (fun t ↦ v₁ (finRotate k t)) v₂)

private theorem norm_walkCov_le [IsProbabilityMeasure P] {k n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w₁ w₂ : Fin k → Fin n) :
    ‖walkCov P ξ η w₁ w₂‖ ≤ 2 * ((n : ℝ)⁻¹ ^ k * B) := by
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) (2 * k)).trans (hη 0)
  have hsingle (v : Fin k → Fin n) :
      ‖∫ ω, walkProd ξ η v ω ∂P‖ ^ 2 ≤ (n : ℝ)⁻¹ ^ k * B := by
    have hL2 : MemLp (walkProd ξ η v) 2 P :=
      memLp_prod_wignerMatrix_apply_two (by simpa using hξp) (by simpa using hηp) v
        fun t ↦ v (finRotate k t)
    have hvar : 0 ≤ (∫ ω, ‖walkProd ξ η v ω‖ ^ 2 ∂P) - (∫ ω, ‖walkProd ξ η v ω‖ ∂P) ^ 2 := by
      simpa only [variance_eq_sub hL2.norm, Pi.pow_apply] using
        variance_nonneg (fun ω ↦ ‖walkProd ξ η v ω‖) P
    have hsq_norm : (∫ ω, ‖walkProd ξ η v ω‖ ^ 2 ∂P) ≤ (n : ℝ)⁻¹ ^ k * B := by
      have hid (ω : Ω) : walkProd ξ η v ω * star (walkProd ξ η v ω) =
          ((‖walkProd ξ η v ω‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
      have heq : ‖∫ ω, walkProd ξ η v ω * star (walkProd ξ η v ω) ∂P‖ =
          ∫ ω, ‖walkProd ξ η v ω‖ ^ 2 ∂P := by
        simp_rw [hid, integral_complex_ofReal, Complex.norm_real,
          Real.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]
      exact heq ▸ norm_integral_walkProd_mul_star_le hξp hηp hξ hη v v
    have hnorm_le : ‖∫ ω, walkProd ξ η v ω ∂P‖ ^ 2 ≤ (∫ ω, ‖walkProd ξ η v ω‖ ∂P) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2
    linarith
  have hmul : ‖(∫ ω, walkProd ξ η w₁ ω ∂P) * star (∫ ω, walkProd ξ η w₂ ω ∂P)‖ ≤
      (n : ℝ)⁻¹ ^ k * B := by
    rw [norm_mul, norm_star]
    have hc : 0 ≤ (n : ℝ)⁻¹ ^ k * B := by positivity
    have hsq : (‖∫ ω, walkProd ξ η w₁ ω ∂P‖ * ‖∫ ω, walkProd ξ η w₂ ω ∂P‖) ^ 2 ≤
        ((n : ℝ)⁻¹ ^ k * B) ^ 2 := by
      rw [mul_pow, sq ((n : ℝ)⁻¹ ^ k * B)]
      exact mul_le_mul (hsingle w₁) (hsingle w₂) (sq_nonneg _) hc
    nlinarith [mul_nonneg (norm_nonneg (∫ ω, walkProd ξ η w₁ ω ∂P))
      (norm_nonneg (∫ ω, walkProd ξ η w₂ ω ∂P))]
  calc
    ‖walkCov P ξ η w₁ w₂‖
      ≤ ‖∫ ω, walkProd ξ η w₁ ω * star (walkProd ξ η w₂ ω) ∂P‖ +
          ‖(∫ ω, walkProd ξ η w₁ ω ∂P) * star (∫ ω, walkProd ξ η w₂ ω ∂P)‖ :=
        norm_sub_le _ _
    _ ≤ (n : ℝ)⁻¹ ^ k * B + (n : ℝ)⁻¹ ^ k * B :=
        add_le_add (norm_integral_walkProd_mul_star_le hξp hηp hξ hη w₁ w₂) hmul
    _ = 2 * ((n : ℝ)⁻¹ ^ k * B) := by ring

private theorem integral_centered_walkProd_mul_star [IsProbabilityMeasure P] {k n : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (w₁ w₂ : Fin k → Fin n) :
    ∫ ω, (walkProd ξ η w₁ ω - ∫ ω', walkProd ξ η w₁ ω' ∂P) *
        star (walkProd ξ η w₂ ω - ∫ ω', walkProd ξ η w₂ ω' ∂P) ∂P =
      walkCov P ξ η w₁ w₂ := by
  have h₁ : Integrable (walkProd ξ η w₁) P :=
    (memLp_prod_wignerMatrix_apply_two (by simpa using hξp) (by simpa using hηp) w₁
      fun t ↦ w₁ (finRotate k t)).integrable one_le_two
  have h₂star : Integrable (fun ω ↦ star (walkProd ξ η w₂ ω)) P :=
    (memLp_prod_wignerMatrix_apply_two (by simpa using hξp) (by simpa using hηp) w₂
      fun t ↦ w₂ (finRotate k t)).star.integrable one_le_two
  have h₁₂ : Integrable (fun ω ↦ walkProd ξ η w₁ ω * star (walkProd ξ η w₂ ω)) P := by
    simp_rw [walkProd_mul_star_eq_prod_sum]
    have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by simp [Nat.two_mul]
    exact integrable_prod_wignerMatrix_apply (by simpa [hcard] using hξp)
      (by simpa [hcard] using hηp) (Sum.elim w₁ fun t ↦ w₂ (finRotate k t))
      (Sum.elim (fun t ↦ w₁ (finRotate k t)) w₂)
  set μ₁ := ∫ ω', walkProd ξ η w₁ ω' ∂P
  set μ₂ := ∫ ω', walkProd ξ η w₂ ω' ∂P
  have hexpand (ω : Ω) :
      (walkProd ξ η w₁ ω - μ₁) * star (walkProd ξ η w₂ ω - μ₂) =
        (walkProd ξ η w₁ ω * star (walkProd ξ η w₂ ω) - walkProd ξ η w₁ ω * star μ₂) -
          (μ₁ * star (walkProd ξ η w₂ ω) - μ₁ * star μ₂) := by
    rw [star_sub]
    ring
  have hL : Integrable (fun ω ↦
      walkProd ξ η w₁ ω * star (walkProd ξ η w₂ ω) - walkProd ξ η w₁ ω * star μ₂) P :=
    h₁₂.sub (h₁.mul_const _)
  have hR : Integrable (fun ω ↦ μ₁ * star (walkProd ξ η w₂ ω) - μ₁ * star μ₂) P :=
    (h₂star.const_mul _).sub (integrable_const _)
  simp_rw [hexpand]
  rw [integral_sub hL hR, integral_sub h₁₂ (h₁.mul_const _),
    integral_sub (h₂star.const_mul _) (integrable_const _),
    integral_mul_const, integral_const_mul]
  simp only [Complex.star_def, integral_conj, integral_const, probReal_univ,
    Complex.real_smul, Complex.ofReal_one, one_mul, walkCov, μ₁, μ₂]
  ring

private theorem integral_norm_inv_mul_trace_pow_sub_sq_eq_re_sum_walkCov [IsProbabilityMeasure P]
    {k n : ℕ} (hk : k ≠ 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P) :
    ∫ ω, ‖(n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k).trace -
        ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k).trace ∂P‖ ^ 2 ∂P =
      (n : ℝ)⁻¹ ^ 2 * (∑ p : (Fin k → Fin n) × (Fin k → Fin n), walkCov P ξ η p.1 p.2).re := by
  let Y (w : Fin k → Fin n) (ω : Ω) : ℂ := walkProd ξ η w ω - ∫ ω', walkProd ξ η w ω' ∂P
  have hwalk2 (w : Fin k → Fin n) : MemLp (walkProd ξ η w) 2 P :=
    memLp_prod_wignerMatrix_apply_two (by simpa using hξp) (by simpa using hηp) w
      fun t ↦ w (finRotate k t)
  have hY2 (w : Fin k → Fin n) : MemLp (Y w) 2 P := (hwalk2 w).sub (memLp_const _)
  have hintY (w₁ w₂ : Fin k → Fin n) : Integrable (fun ω ↦ Y w₁ ω * star (Y w₂ ω)) P :=
    memLp_one_iff_integrable.mp ((hY2 w₁).fun_mul (hY2 w₂).star (r := 1))
  have htr_sub (ω : Ω) :
      (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k).trace -
        ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k).trace ∂P =
      (n : ℂ)⁻¹ * ∑ w : Fin k → Fin n, Y w ω := by
    rw [integral_const_mul, ← mul_sub, trace_pow_eq_sum_prod _ hk]
    simp_rw [trace_pow_eq_sum_prod _ hk]
    rw [integral_finsetSum _ fun w _ ↦ (hwalk2 w).integrable one_le_two, ← sum_sub_distrib]
  have hpt (ω : Ω) : ‖(n : ℂ)⁻¹ * ∑ w : Fin k → Fin n, Y w ω‖ ^ 2 =
      (n : ℝ)⁻¹ ^ 2 * (∑ w₁, ∑ w₂, Y w₁ ω * star (Y w₂ ω)).re := by
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast, inv_pow]
    congr 1
    have hz : (∑ w : Fin k → Fin n, Y w ω) * star (∑ w : Fin k → Fin n, Y w ω) =
        ((‖∑ w : Fin k → Fin n, Y w ω‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    have hre := ((congrArg Complex.re hz).trans (Complex.ofReal_re _)).symm
    rw [star_sum, sum_mul] at hre
    simpa only [mul_sum] using hre
  simp_rw [htr_sub, hpt, integral_const_mul]
  congr 1
  have hsum_int : Integrable (fun ω ↦ ∑ w₁, ∑ w₂, Y w₁ ω * star (Y w₂ ω)) P :=
    integrable_finsetSum _ fun w₁ _ ↦ integrable_finsetSum _ fun w₂ _ ↦ hintY w₁ w₂
  rw [show (∫ ω, (∑ w₁, ∑ w₂, Y w₁ ω * star (Y w₂ ω)).re ∂P) =
      (∫ ω, ∑ w₁, ∑ w₂, Y w₁ ω * star (Y w₂ ω) ∂P).re from by
    simpa only [RCLike.re_to_complex] using integral_re hsum_int]
  congr 1
  rw [integral_finsetSum _ fun w₁ _ ↦ integrable_finsetSum _ fun w₂ _ ↦ hintY w₁ w₂]
  simp_rw [integral_finsetSum _ fun w₂ _ ↦ hintY _ w₂]
  dsimp only [Y]
  simp_rw [integral_centered_walkProd_mul_star hξp hηp]
  rw [← Fintype.sum_prod_type']

/-- **Centered second moment of normalized Wigner traces.** For independent centered entries on a
probability space with `2 * k`-th absolute moments bounded by `B`, the centered second moment of
`(n : ℂ)⁻¹ * tr(Hₙᵏ)` is at most `2 * k ^ (2 * k) * B / n ^ 2`, for every `k, n : ℕ`. -/
theorem integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le [IsProbabilityMeasure P]
    {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∫ ω, ‖(n : ℂ)⁻¹ * (wignerMatrix ξ η n ω ^ k).trace -
        ∫ ω', (n : ℂ)⁻¹ * (wignerMatrix ξ η n ω' ^ k).trace ∂P‖ ^ 2 ∂P ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n : ℝ) ^ 2 := by
  classical
  have hB : 0 ≤ B :=
    (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) (2 * k)).trans (hη 0)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases eq_or_ne k 0 with rfl | hk
  · suffices 0 ≤ 2 * B / (n : ℝ) ^ 2 by simpa
    positivity
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  let S : Finset ((Fin k → Fin n) × (Fin k → Fin n)) :=
    {p | (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))) ∧
      ∀ s : Fin k ⊕ Fin k, ∃ s' ≠ s,
        Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
          (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s' =
        Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
          (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s}
  have hfilter : (∑ p : (Fin k → Fin n) × (Fin k → Fin n), walkCov P ξ η p.1 p.2) =
      ∑ p ∈ S, walkCov P ξ η p.1 p.2 := by
    refine (Finset.sum_filter_of_ne fun p _ hp ↦ ?_).symm
    have hξm : ∀ ij, AEMeasurable (ξ ij) P := fun ij ↦ (hξp ij).aestronglyMeasurable.aemeasurable
    have hηm : ∀ i, AEMeasurable (η i) P := fun i ↦ (hηp i).aestronglyMeasurable.aemeasurable
    refine ⟨by_contra fun hdisj ↦ hp (walkCov_eq_zero_of_disjoint_edges hindep hξm hηm
      (memLp_prod_wignerMatrix_apply_two (by simpa using hξp) (by simpa using hηp) p.1
        fun t ↦ p.1 (finRotate k t)).aestronglyMeasurable
      (memLp_prod_wignerMatrix_apply_two (by simpa using hξp) (by simpa using hηp) p.2
        fun t ↦ p.2 (finRotate k t)).aestronglyMeasurable hdisj),
      by_contra fun hsing ↦ hp (walkCov_eq_zero_of_singleton_edge hindep hξm hηm hξzero hηzero
        p.1 p.2 hsing)⟩
  have hcardS : (#S : ℝ) ≤ (n : ℝ) ^ k * (k : ℝ) ^ (2 * k) := by
    exact_mod_cast (card_filter_shared_edge_and_no_singleton_edge_le (α := Fin n) hk).trans_eq
      (by simp)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [integral_norm_inv_mul_trace_pow_sub_sq_eq_re_sum_walkCov hk hξp hηp, hfilter]
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ p ∈ S, walkCov P ξ η p.1 p.2).re
      ≤ (n : ℝ)⁻¹ ^ 2 * ‖∑ p ∈ S, walkCov P ξ η p.1 p.2‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ ^ 2 * ∑ p ∈ S, ‖walkCov P ξ η p.1 p.2‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ ^ 2 * ∑ _p ∈ S, 2 * ((n : ℝ)⁻¹ ^ k * B) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun p _ ↦ norm_walkCov_le hξp hηp hξ hη p.1 p.2)
          (by positivity)
    _ = (n : ℝ)⁻¹ ^ 2 * ((#S : ℝ) * (2 * ((n : ℝ)⁻¹ ^ k * B))) := by simp
    _ ≤ (n : ℝ)⁻¹ ^ 2 * (((n : ℝ) ^ k * (k : ℝ) ^ (2 * k)) * (2 * ((n : ℝ)⁻¹ ^ k * B))) := by
        gcongr
    _ = 2 * (k : ℝ) ^ (2 * k) * B / (n : ℝ) ^ 2 := by rw [inv_pow, inv_pow]; field_simp

end Covariance

section SpectralVariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- **Variance bound for Wigner empirical spectral moments.** For independent centered entries on a
probability space with `2 * k`-th absolute moments bounded by `B`, the variance of the `k`-th
empirical spectral moment of `Hₙ₊₁` is at most `2 * k ^ (2 * k) * B / (n + 1) ^ 2`. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le (k n : ℕ) {B : ℝ}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  let X : Ω → ℝ := fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)
  let Z : Ω → ℂ := fun ω ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace
  have hX2 : MemLp X 2 P := memLp_integral_pow_spectralMeasure_wignerMatrix_two hξp hηp n
  have hZ2 : MemLp Z 2 P := (memLp_trace_pow_wignerMatrix_two hξp hηp (n + 1)).const_mul _
  have hXZ (ω : Ω) : X ω = (Z ω).re := by
    simp only [X, Z, Matrix.integral_pow_spectralMeasure, Fintype.card_fin, RCLike.re_to_complex,
      ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hmean : ∫ ω', X ω' ∂P = (∫ ω', Z ω' ∂P).re := by
    simp_rw [hXZ]
    simpa only [RCLike.re_to_complex] using integral_re (hZ2.integrable one_le_two)
  have hpt (ω : Ω) : (X ω - ∫ ω', X ω' ∂P) ^ 2 ≤ ‖Z ω - ∫ ω', Z ω' ∂P‖ ^ 2 := by
    rw [hXZ ω, hmean, ← Complex.sub_re, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  rw [variance_eq_integral hX2.aemeasurable]
  refine (integral_mono ((hX2.sub (memLp_const _)).integrable_sq)
    ((hZ2.sub (memLp_const _)).integrable_norm_pow two_ne_zero) hpt).trans ?_
  simpa only [Z, Pi.sub_apply, Nat.cast_add, Nat.cast_one] using
    integral_norm_inv_mul_trace_pow_wignerMatrix_sub_sq_le (n := n + 1) hindep hξzero hηzero
      hξp hηp hξ hη

/-- **Chebyshev tail bound for Wigner empirical spectral moments.** Under independent centered
entries with `2 * k`-th absolute moments bounded by `B`, deviations of the `k`-th empirical
spectral moment of `Hₙ₊₁` from its mean satisfy an `O_k((n + 1)⁻² / ε²)` tail bound. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge (k n : ℕ) {B : ℝ}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
        ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
          (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have hmem := memLp_integral_pow_spectralMeasure_wignerMatrix_two hξp hηp n
  refine (meas_ge_le_variance_div_sq hmem hε).trans ?_
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (variance_integral_pow_spectralMeasure_wignerMatrix_le k n hindep hξzero hηzero hξp hηp hξ hη)
    (sq_nonneg ε))

end SpectralVariance

/-- Fluctuations of the `k`-th empirical spectral moment around its mean vanish in probability for
triangular Wigner arrays with independent centered entries and uniformly bounded `2 * k`-th
absolute moments. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    (k : ℕ) {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun j : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) j) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0) (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
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
    · ext n
      simp [div_eq_mul_inv, inv_pow]
    · simp
  have hbound : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ bot_le) (fun n ↦ measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge k n
      (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) hε)

end TauCeti.Probability
