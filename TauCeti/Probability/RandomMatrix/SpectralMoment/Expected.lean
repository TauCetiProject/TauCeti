/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Combinatorics.TreeWalk.Pairing
public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.RandomMatrix.MomentBounds
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Expected spectral moments of Wigner matrices

Combining the leading-word expectation formula
(`TauCeti.integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one`), the Catalan
enumeration of leading cyclic trace words
(`TauCeti.TreeWalk.card_filter_no_singleton_edge_and_card_image_eq`), and the nonleading remainder
estimates (`TauCeti.norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le` and
`TauCeti.norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le`) yields the asymptotic
moments of Wigner matrices:

* the normalized expected even trace `(n : ℂ)⁻¹ * E[tr(Hₙ^(2m))]` converges to `(catalan m : ℂ)`;
* for every `k : ℕ`, the expected `k`-th moment of the empirical spectral measure of `Hₙ₊₁`
  converges to the `k`-th moment `∫ x, x ^ k ∂semicircleReal 0 1` of the standard semicircle law.

Because the finite-`n` remainder bounds depend on the entry distributions only through the uniform
`k`-th absolute moment bound `B`, all limit theorems hold both for triangular arrays `(Ω n, P n,
ξ n, η n)` on varying probability spaces and for a single infinite Wigner array.

## Main results

* `TauCeti.Probability.sum_integral_prod_wignerMatrix_apply_leading`: exact evaluation of the
  leading-word trace sum as `(n.descFactorial (m + 1) * catalan m) * n⁻ᵐ`.
* `TauCeti.Probability.norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_descFactorial_le`:
  quantitative `O(n⁻¹)` remainder bound for normalized expected even traces.
* `TauCeti.Probability.integrable_integral_pow_spectralMeasure_wignerMatrix`: integrability of the
  `k`-th empirical spectral moment from `Lᵏ` entry bounds.
* `TauCeti.Probability.tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix_array` and
  `TauCeti.Probability.tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix`: normalized
  expected `2m`-th traces converge to `catalan m`.
* `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix_array` and
  `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix`: expected `k`-th
  empirical spectral moments converge to `∫ x, x ^ k ∂semicircleReal 0 1`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open TauCeti TauCeti.TreeWalk
open scoped Topology

namespace TauCeti.Probability

section FixedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- For `m ≠ 0`, independent upper-triangular entries with unit second absolute moments give
`(n.descFactorial (m + 1) * catalan m) * (n : ℂ)⁻¹ ^ m` for the sum of expected Wigner products
over singleton-free cyclic words of length `2 * m` visiting `m + 1` vertices. -/
theorem sum_integral_prod_wignerMatrix_apply_leading {m : ℕ} (hm : m ≠ 0)
    (hindep : iIndepFun ξ P) (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1) (n : ℕ) :
    (∑ w : Fin (2 * m) → Fin n with
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1,
      ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) =
      (n.descFactorial (m + 1) * catalan m : ℕ) * (n : ℂ)⁻¹ ^ m := by
  have hterm (w : Fin (2 * m) → Fin n)
      (hw : w ∈ ({w : Fin (2 * m) → Fin n |
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1} : Finset _)) :
      ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P = (n : ℂ)⁻¹ ^ m := by
    obtain ⟨hno, hv⟩ := (mem_filter.mp hw).2
    exact integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one
      hindep hsecond w hno hv
  rw [sum_congr rfl hterm, sum_const,
    card_filter_no_singleton_edge_and_card_image_eq (α := Fin n) hm, Fintype.card_fin,
    nsmul_eq_mul]

/-- Quantitative `O(n⁻¹)` remainder bound between the normalized expected `2m`-th Wigner trace and
`((n.descFactorial (m + 1) : ℂ) / n ^ (m + 1)) * catalan m`, for `m ≠ 0`. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_descFactorial_le
    [IsFiniteMeasure P] {m n : ℕ} (hm : m ≠ 0) {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
        ((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) * (catalan m : ℂ)‖ ≤
      (m : ℝ) ^ (2 * m) * B / n := by
  have hindepξ : iIndepFun ξ P := by
    simpa only [Function.comp_def, Sum.elim_inl] using
      iIndepFun.precomp (@Sum.inl_injective StrictUpper ℕ) hindep
  have hbound := norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le
    hindep hξzero hηzero hm hξp hηp hξ hη (n := n)
  rw [sum_integral_prod_wignerMatrix_apply_leading hm hindepξ hsecond n] at hbound
  have hlead : (n : ℂ)⁻¹ * ((n.descFactorial (m + 1) * catalan m : ℕ) * (n : ℂ)⁻¹ ^ m) =
      ((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) * (catalan m : ℂ) := by
    push_cast
    rw [pow_succ, div_eq_mul_inv, mul_inv]
    ring
  simpa only [mul_sub, hlead] using hbound

/-- When the entries of the Wigner array lie in `Lᵏ` on a finite measure space, the `k`-th
empirical spectral moment of `wignerMatrix ξ η (n + 1)` is integrable. -/
theorem integrable_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P) (n : ℕ) :
    Integrable (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have htr : Integrable (fun ω ↦ (wignerMatrix ξ η (n + 1) ω ^ k).trace) P := by
      simp_rw [trace_pow_eq_sum_prod _ hk]
      exact integrable_finsetSum _ fun w _ ↦
        integrable_prod_wignerMatrix_apply (by simpa using hξp) (by simpa using hηp) _ _
    simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin, RCLike.re_to_complex]
    exact htr.re.const_mul _

end FixedSpace

section Asymptotics

private theorem tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix_of_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {sz : ℕ → ℕ} (hsz : Tendsto sz atTop atTop) (m : ℕ) {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) k) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0) (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * m : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * m : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * m) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * m) ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦
        (sz n : ℂ)⁻¹ * ∫ ω, (wignerMatrix (ξ n) (η n) (sz n) ω ^ (2 * m)).trace ∂P n)
      atTop (𝓝 (catalan m : ℂ)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsz.eventually_ge_atTop 1] with n hn
    have hn0 : (sz n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp [hn0]
  · have hlim0 : Tendsto (fun n : ℕ ↦ (m : ℝ) ^ (2 * m) * B / (sz n : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).comp hsz
    have hrem : Tendsto (fun n : ℕ ↦
        (sz n : ℂ)⁻¹ * (∫ ω, (wignerMatrix (ξ n) (η n) (sz n) ω ^ (2 * m)).trace ∂P n) -
          (((sz n).descFactorial (m + 1) : ℂ) / (sz n : ℂ) ^ (m + 1)) * (catalan m : ℂ))
        atTop (𝓝 0) :=
      squeeze_zero_norm
        (fun n ↦ norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_descFactorial_le hm
          (hindep n) (hξzero n) (hηzero n) (hsecond n) (hξp n) (hηp n) (hξ n) (hη n)) hlim0
    have hdesc : Tendsto (fun n : ℕ ↦ (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1))
        atTop (𝓝 1) := by
      have hprod : Tendsto (fun n : ℕ ↦ ∏ i ∈ range (m + 1), (1 - (i : ℝ) / n))
          atTop (𝓝 (∏ _i ∈ range (m + 1), (1 : ℝ))) :=
        tendsto_finsetProd (range (m + 1)) fun i _ ↦ by
          simpa using tendsto_const_nhds.sub
            (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
      simp only [prod_const_one] at hprod
      refine hprod.congr' ?_
      filter_upwards [eventually_ge_atTop (m + 2)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
        show (n : ℝ) ^ (m + 1) = ∏ _i ∈ range (m + 1), (n : ℝ) by simp, ← prod_div_distrib]
      refine prod_congr rfl fun i hi ↦ ?_
      have hin : i ≤ n := le_of_lt ((mem_range.mp hi).trans_le (by omega))
      rw [Nat.cast_sub hin, sub_div, div_self hn0]
    have hmain : Tendsto (fun n : ℕ ↦
        (((sz n).descFactorial (m + 1) : ℂ) / (sz n : ℂ) ^ (m + 1)) * (catalan m : ℂ))
        atTop (𝓝 (catalan m : ℂ)) := by
      have hratio : Tendsto (fun n : ℕ ↦ (n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1))
          atTop (𝓝 1) := by
        simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_pow,
          Complex.ofReal_natCast, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hdesc
      simpa only [Function.comp_def, one_mul] using (hratio.mul_const (catalan m : ℂ)).comp hsz
    simpa only [sub_add_cancel, zero_add] using hrem.add hmain

/-- **Expected even traces of triangular Wigner arrays.** For independent centered entries on
varying probability spaces with unit off-diagonal second absolute moments and `2m`-th absolute
moments uniformly bounded by `B`, the normalized expected `2m`-th trace converges to `catalan m`. -/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    (m : ℕ) {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) k) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0) (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * m : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * m : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * m) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * m) ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹ * ∫ ω, (wignerMatrix (ξ n) (η n) n ω ^ (2 * m)).trace ∂P n)
      atTop (𝓝 (catalan m : ℂ)) :=
  tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix_of_tendsto tendsto_id m hindep
    hξzero hηzero hsecond hξp hηp hξ hη

/-- **Expected even traces of Wigner matrices.** For a single infinite array of independent
centered entries on a probability space with unit off-diagonal second absolute moments and
uniformly bounded `2m`-th absolute moments, `(n : ℂ)⁻¹ * E[tr(Hₙ^(2m))]` tends to `catalan m`. -/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} (m : ℕ) {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P)
      atTop (𝓝 (catalan m : ℂ)) :=
  tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix_array m (fun _ ↦ hindep)
    (fun _ ↦ hξzero) (fun _ ↦ hηzero) (fun _ ↦ hsecond) (fun _ ↦ hξp) (fun _ ↦ hηp)
    (fun _ ↦ hξ) (fun _ ↦ hη)

/-- **Expected spectral moments of triangular Wigner arrays.** For every `k : ℕ`, if a sequence of
Wigner arrays on varying probability spaces has independent centered entries, unit off-diagonal
second absolute moments, and `k`-th absolute moments uniformly bounded by `B`, then the expected
`k`-th empirical spectral moment of `Hₙ₊₁` converges to the `k`-th moment of the standard
semicircle law `semicircleReal 0 1`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    (k : ℕ) {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun j : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) j) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0) (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) k (P n)) (hηp : ∀ n i, MemLp (η n i) k (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B) (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∫ x, x ^ k
        ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have heq (n : ℕ) : (∫ ω, (∫ x, x ^ k
        ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n) =
      (((n + 1 : ℕ) : ℂ)⁻¹ *
        ∫ ω, (wignerMatrix (ξ n) (η n) (n + 1) ω ^ k).trace ∂P n).re := by
    have htr : Integrable (fun ω ↦ (wignerMatrix (ξ n) (η n) (n + 1) ω ^ k).trace) (P n) := by
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · simp_rw [trace_pow_eq_sum_prod _ hk]
        exact integrable_finsetSum _ fun w _ ↦
          integrable_prod_wignerMatrix_apply (by simpa using hξp n) (by simpa using hηp n) _ _
    simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin]
    rw [integral_const_mul, integral_re htr]
    simp only [RCLike.re_to_complex]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [heq]
  rcases k.even_or_odd' with ⟨m, rfl | rfl⟩
  · have htr := tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix_of_tendsto
      (tendsto_add_atTop_nat 1) m hindep hξzero hηzero hsecond
      (by simpa using hξp) (by simpa using hηp) hξ hη
    simpa only [Function.comp_def, integral_pow_two_mul_semicircleReal_zero, NNReal.coe_one,
      one_pow, one_mul, Complex.natCast_re] using
      Complex.continuous_re.continuousAt.tendsto.comp htr
  · have hlim : Tendsto
        (fun n : ℕ ↦ (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_div] using
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
    have htr : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∫ ω, (wignerMatrix (ξ n) (η n) (n + 1) ω ^ (2 * m + 1)).trace ∂P n)
        atTop (𝓝 0) :=
      squeeze_zero_norm
        (fun n ↦ norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le
          (hindep n) (hξzero n) (hηzero n) (by simpa using hξp n) (by simpa using hηp n)
          (hξ n) (hη n)) hlim
    simpa only [Function.comp_def, integral_pow_two_mul_add_one_semicircleReal_zero,
      Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp htr

/-- **Expected spectral moments of Wigner matrices.** For every `k : ℕ`, if a Wigner array has
independent centered entries, unit off-diagonal second absolute moments, and uniformly bounded
`k`-th absolute moments, then the expected `k`-th empirical spectral moment of `Hₙ₊₁` converges to
`∫ x, x ^ k ∂semicircleReal 0 1`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} (k : ℕ) {B : ℝ}
    (hindep : iIndepFun (fun j : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) j) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∫ x, x ^ k
        ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) :=
  tendsto_integral_pow_spectralMeasure_wignerMatrix_array k (fun _ ↦ hindep)
    (fun _ ↦ hξzero) (fun _ ↦ hηzero) (fun _ ↦ hsecond) (fun _ ↦ hξp) (fun _ ↦ hηp)
    (fun _ ↦ hξ) (fun _ ↦ hη)

end Asymptotics

end TauCeti.Probability
