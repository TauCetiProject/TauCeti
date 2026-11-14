/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Count
public import TauCeti.Combinatorics.TreeWalk.ConnectedPair
public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.RandomMatrix.MomentBounds
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Expected spectral moments and variance bounds for Wigner matrices

This file completes the moment-method estimates for Hermitian Wigner matrices of all moment
orders `k : ℕ`:

1. **Expected moments.** Combining the Catalan-times-descending-factorial count of leading cyclic
   trace words (`card_filter_leadingCyclicWord`) with the `n⁻ᵐ` expectation of each leading word
   and the `O(n⁻¹)` / `O(n⁻¹/²)` bounds on nonleading and odd words (`MomentBounds`), the expected
   `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)` converges to the `k`th moment of
   the standard semicircle law `semicircleReal 0 1` (`catalan m` for `k = 2 * m` and `0` for odd
   `k`).
2. **`O_k(n⁻²)` variance bounds and concentration.** Expanding the variance of the `k`th empirical
   spectral moment over pairs of cyclic trace words `(w₁, w₂)`, pairs with disjoint unordered edge
   sets cancel by independence and pairs whose combined step family contains a singleton unordered
   edge vanish by centering. The remaining pairs share an unordered edge and have no combined
   singleton unordered edge, so there are at most `(n + 1) ^ k * k ^ (2 * k)` of them
   (`card_filter_connectedPair_le`), each bounded in magnitude by `2 * (n + 1)⁻¹ ^ k * B`. This
   gives `Var[∫ x ^ k dL_{H_{n+1}}] ≤ 2 * k ^ (2 * k) * B / (n + 1) ^ 2`, Chebyshev tail bounds,
   convergence in probability on varying sample spaces, and Borel–Cantelli almost-sure convergence
   without any coupling assumption across matrix sizes `n`.

## Main results

* `TauCeti.Probability.norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le` and
  `TauCeti.Probability.abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le`:
  quantitative `O(n⁻¹)` error bounds between expected even Wigner spectral moments and the Catalan
  numbers.
* `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix`: convergence of expected
  `k`th empirical spectral moments to the `k`th moments of `semicircleReal 0 1`.
* `TauCeti.Probability.variance_integral_pow_spectralMeasure_wignerMatrix_le`: quantitative
  `2 * k ^ (2 * k) * B / (n + 1) ^ 2` bound on the variance of the `k`th empirical spectral moment.
* `TauCeti.Probability.tendsto_integral_pow_spectralMeasure_wignerMatrix_probability`: convergence
  in probability of the `k`th empirical spectral moment on possibly varying sample spaces.
* `TauCeti.Probability.ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq` and
  `TauCeti.Probability.ae_tendsto_integral_pow_spectralMeasure_wignerMatrix`: almost-sure
  convergence of the `k`th empirical spectral moment via Borel–Cantelli.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemmas 2.1.6 and 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology ENNReal

namespace TauCeti.Probability

section ArithmeticHelpers

private theorem pow_le_descFactorial_add_choose_two_mul_pow (n : ℕ) :
    ∀ k : ℕ, n ^ (k + 1) ≤ n.descFactorial (k + 1) + (k + 1).choose 2 * n ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := Nat.mul_le_mul_right n (pow_le_descFactorial_add_choose_two_mul_pow n k)
    have hmul := Nat.descFactorial_mul_self n (k + 1)
    have hle := Nat.mul_le_mul_left (k + 1) (Nat.descFactorial_le_pow n (k + 1))
    have hchoose : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
      simpa using Nat.choose_succ_succ (k + 1) 1
    calc
      n ^ (k + 2) = n ^ (k + 1) * n := pow_succ n (k + 1)
      _ ≤ (n.descFactorial (k + 1) + (k + 1).choose 2 * n ^ k) * n := ih
      _ = n.descFactorial (k + 2) + (k + 1) * n.descFactorial (k + 1) +
            (k + 1).choose 2 * n ^ (k + 1) := by
        rw [Nat.add_mul, hmul, Nat.mul_assoc, ← pow_succ]
      _ ≤ n.descFactorial (k + 2) + (k + 1) * n ^ (k + 1) +
            (k + 1).choose 2 * n ^ (k + 1) :=
        Nat.add_le_add_right (Nat.add_le_add_left hle _) _
      _ = n.descFactorial (k + 2) + (k + 2).choose 2 * n ^ (k + 1) := by
        rw [hchoose]
        ring

private theorem norm_descFactorial_div_pow_sub_one_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    ‖((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) - 1‖ ≤
      ((m + 1).choose 2 : ℝ) / n := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hle_pow : (n.descFactorial (m + 1) : ℝ) ≤ (n : ℝ) ^ (m + 1) := by
    exact_mod_cast Nat.descFactorial_le_pow n (m + 1)
  have hlow : (n : ℝ) ^ (m + 1) ≤
      (n.descFactorial (m + 1) : ℝ) + ((m + 1).choose 2 : ℝ) * (n : ℝ) ^ m := by
    exact_mod_cast pow_le_descFactorial_add_choose_two_mul_pow n m
  have hcast : ((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) - 1 =
      ((((n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1)) - 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hdiv_le : (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr hle_pow
  rw [abs_of_nonpos (sub_nonpos.mpr hdiv_le), neg_sub]
  rw [le_div_iff₀ hnpos]
  have hpow : (1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1)) * (n : ℝ) ^ (m + 1) =
      (n : ℝ) ^ (m + 1) - (n.descFactorial (m + 1) : ℝ) := by
    field_simp
  have hscale : (1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1)) * n * (n : ℝ) ^ m =
      (n : ℝ) ^ (m + 1) - (n.descFactorial (m + 1) : ℝ) := by
    calc
      (1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1)) * n * (n : ℝ) ^ m =
          (1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1)) * (n : ℝ) ^ (m + 1) := by
        rw [pow_succ', mul_assoc]
      _ = (n : ℝ) ^ (m + 1) - (n.descFactorial (m + 1) : ℝ) := hpow
  have hpm : (0 : ℝ) < (n : ℝ) ^ m := by positivity
  nlinarith

private theorem pow_le_one_add_pow_two_mul (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ k ≤ 1 + x ^ (2 * k) := by
  rcases le_or_gt x 1 with h1 | h1
  · have hpow : x ^ k ≤ 1 := pow_le_one₀ hx h1
    have hnn : 0 ≤ x ^ (2 * k) := pow_nonneg hx _
    linarith
  · have hpow : x ^ k ≤ x ^ (2 * k) := pow_le_pow_right₀ h1.le (by omega)
    linarith

end ArithmeticHelpers

section SpectralTraceBridge

/-- The normalized trace of `H ^ k` for a Wigner matrix `H` equals its real `k`th spectral moment
embedded in `ℂ`. -/
theorem inv_mul_trace_pow_wignerMatrix_eq_ofReal_integral {Ω : Type*}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} (n k : ℕ) (ω : Ω) :
    ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace =
      ((∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) : ℝ) : ℂ) := by
  let hH := wignerMatrix_isHermitian ξ η ω (n + 1)
  rw [Matrix.integral_spectralMeasure _ hH, smul_eq_mul, hH.trace_pow_eq_sum_eigenvalues_pow]
  simp [Fintype.card_fin]

end SpectralTraceBridge

section ExpectedMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Summing the expected entry products over all leading cyclic Wigner words of length `2 * m`
(`m ≠ 0`) yields `(catalan m * n.descFactorial (m + 1)) * n⁻ᵐ` whenever the upper-triangular
entries are independent with unit second absolute moments. -/
theorem sum_integral_prod_wignerMatrix_leading_eq {m : ℕ} (hm : m ≠ 0)
    (hindep : iIndepFun ξ P) (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1) (n : ℕ) :
    ∑ w : Fin (2 * m) → Fin n with
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1,
      (∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) =
      (catalan m * n.descFactorial (m + 1) : ℂ) * (n : ℂ)⁻¹ ^ m := by
  have : NeZero m := ⟨hm⟩
  have hterm : ∀ w ∈ ({w : Fin (2 * m) → Fin n |
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} : Finset _),
      (∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) = (n : ℂ)⁻¹ ^ m := by
    intro w hw
    obtain ⟨hns, hv⟩ := (mem_filter.mp hw).2
    exact integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one
      hindep hsecond w hns hv
  rw [sum_congr rfl hterm, sum_const, TreeWalk.card_filter_leadingCyclicWord]
  simp [Fintype.card_fin]

/-- Quantitative `O(n⁻¹)` error bound between the expected even normalized Wigner trace of degree
`2 * m` and the Catalan number `catalan m`, for `n ≠ 0`. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le {m n : ℕ}
    (hn : n ≠ 0) {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ)‖ ≤
      ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / n := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rcases eq_or_ne m 0 with rfl | hm
  · have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) 0).trans (hη 0)
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp [hnc, div_nonneg hB (Nat.cast_nonneg n)]
  · let S := ∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P
    have hrem := norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le
      hindep hξzero hηzero hm hξp hηp hξ hη (n := n)
    have hindepξ : iIndepFun ξ P := by
      simpa only [Sum.elim_inl] using hindep.precomp (g := Sum.inl) Sum.inl_injective
    have hlead : (n : ℂ)⁻¹ * S - (catalan m : ℂ) =
        (catalan m : ℂ) * (((n.descFactorial (m + 1) : ℂ) / (n : ℂ) ^ (m + 1)) - 1) := by
      dsimp only [S]
      rw [sum_integral_prod_wignerMatrix_leading_eq (η := η) hm hindepξ hsecond n]
      rw [inv_pow, pow_succ', div_eq_mul_inv, mul_inv]
      ring
    have hsplit : (n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ) =
        (n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - S) +
          ((n : ℂ)⁻¹ * S - (catalan m : ℂ)) := by ring
    rw [hsplit]
    calc
      ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - S) +
          ((n : ℂ)⁻¹ * S - (catalan m : ℂ))‖
        ≤ ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - S)‖ +
            ‖(n : ℂ)⁻¹ * S - (catalan m : ℂ)‖ := norm_add_le _ _
      _ ≤ (m : ℝ) ^ (2 * m) * B / n +
            (catalan m : ℝ) * (((m + 1).choose 2 : ℝ) / n) := by
        gcongr
        rw [hlead, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (norm_descFactorial_div_pow_sub_one_le hn m) (by positivity)
      _ = ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / n := by ring

/-- Quantitative `O(n⁻¹)` error bound between the expected `2 * m`th empirical spectral moment of
`wignerMatrix ξ η (n + 1)` and the `2 * m`th moment of `semicircleReal 0 1`. -/
theorem abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le {m n : ℕ}
    {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    |(∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) -
      ∫ x, x ^ (2 * m) ∂semicircleReal 0 1| ≤
      ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / (n + 1 : ℝ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have heq : (∫ ω, ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ (2 * m)).trace ∂P) =
      ((∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P : ℝ) : ℂ) := by
    simp_rw [inv_mul_trace_pow_wignerMatrix_eq_ofReal_integral n (2 * m)]
    exact integral_complex_ofReal
  have h := norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le (n := n + 1)
    (Nat.succ_ne_zero n) hindep hξzero hηzero hsecond hξp hηp hξ hη
  rw [← integral_const_mul, heq] at h
  rw [integral_pow_two_mul_semicircleReal_zero, NNReal.coe_one, one_pow, one_mul]
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using h

/-- Quantitative `O(n⁻¹/²)` bound on the expected `(2 * m + 1)`st empirical spectral moment of
`wignerMatrix ξ η (n + 1)`. -/
theorem abs_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le {m n : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℝ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have heq : (∫ ω, ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ (2 * m + 1)).trace ∂P) =
      ((∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P : ℝ) : ℂ) := by
    simp_rw [inv_mul_trace_pow_wignerMatrix_eq_ofReal_integral n (2 * m + 1)]
    exact integral_complex_ofReal
  have h := norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le (n := n + 1)
    hindep hξzero hηzero hξp hηp hξ hη
  rw [← integral_const_mul, heq] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using h

/-- For Wigner matrices on (possibly varying) probability spaces with independent centered entries,
unit off-diagonal second moments, and uniformly bounded `k`th absolute moments, the expected `k`th
empirical spectral moment converges to the `k`th moment of `semicircleReal 0 1`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (k : ℝ≥0∞) (P n))
    (hηp : ∀ n i, MemLp (η n i) (k : ℝ≥0∞) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        ((catalan m * (m + 1).choose 2 : ℝ) + (m : ℝ) ^ (2 * m) * B) / (n + 1 : ℝ))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hlim
    simpa only [Real.norm_eq_abs] using
      abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_semicircleReal_le
        (hindep n) (hξzero n) (hηzero n) (hsecond n)
        (by simpa using hξp n) (by simpa using hηp n) (hξ n) (hη n)
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ ↦
        (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hlim
    simpa only [sub_zero, Real.norm_eq_abs] using
      abs_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le
        (hindep n) (hξzero n) (hηzero n)
        (by simpa using hξp n) (by simpa using hηp n) (hξ n) (hη n)

end ExpectedMoments

section VarianceAndConcentration

private def wignerCoord {n : ℕ} (i j : Fin n) : StrictUpper ⊕ ℕ :=
  if h : i.val < j.val then .inl ⟨(i, j), h⟩
  else if h' : j.val < i.val then .inl ⟨(j, i), h'⟩ else .inr i

private theorem wignerCoord_eq_iff {n : ℕ} {i j i' j' : Fin n} :
    wignerCoord i j = wignerCoord i' j' ↔ s(i, j) = s(i', j') := by
  unfold wignerCoord
  split_ifs <;> simp [Fin.ext_iff] <;> omega

private def wignerOrient {n : ℕ} (i j : Fin n) (z : ℂ) : ℂ :=
  if i.val < j.val then z else if j.val < i.val then star z else (z.re : ℂ)

private theorem measurable_wignerOrient {n : ℕ} (i j : Fin n) :
    Measurable (wignerOrient i j) := by
  unfold wignerOrient
  split_ifs
  · exact measurable_id
  · exact continuous_star.measurable
  · exact Complex.measurable_ofReal.comp Complex.measurable_re

private theorem wignerMatrix_apply_eq_wignerOrient {Ω : Type*} {ξ : StrictUpper → Ω → ℂ}
    {η : ℕ → Ω → ℝ} {n : ℕ} (ω : Ω) (i j : Fin n) :
    wignerMatrix ξ η n ω i j = (Real.sqrt n : ℂ)⁻¹ *
      wignerOrient i j (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) (wignerCoord i j) ω) := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [wignerOrient, wignerCoord, h]
  · obtain rfl := Fin.ext h
    simp [wignerOrient, wignerCoord]
  · simp [wignerOrient, wignerCoord, h, h.not_gt]

/-- Products of Wigner matrix entries over two finite index families whose unordered edge sets are
disjoint are independent, so the expectation of their product factors. -/
theorem integral_prod_mul_prod_wignerMatrix_apply_eq_mul_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (hξm : ∀ ij, AEMeasurable (ξ ij) P) (hηm : ∀ i, AEMeasurable (η i) P)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    {n : ℕ} (u₁ v₁ : ι₁ → Fin n) (u₂ v₂ : ι₂ → Fin n)
    (hdisj : ∀ s t, s(u₁ s, v₁ s) ≠ s(u₂ t, v₂ t)) :
    ∫ ω, (∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s)) *
        (∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) ∂P =
      (∫ ω, ∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s) ∂P) *
        (∫ ω, ∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t) ∂P) := by
  classical
  let X : StrictUpper ⊕ ℕ → Ω → ℂ := fun k ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k
  let e₁ : ι₁ → StrictUpper ⊕ ℕ := fun s ↦ wignerCoord (u₁ s) (v₁ s)
  let e₂ : ι₂ → StrictUpper ⊕ ℕ := fun t ↦ wignerCoord (u₂ t) (v₂ t)
  let S₁ : Finset (StrictUpper ⊕ ℕ) := univ.image e₁
  let S₂ : Finset (StrictUpper ⊕ ℕ) := univ.image e₂
  have hS₁₂ : Disjoint S₁ S₂ := by
    rw [disjoint_left]
    intro c hc₁ hc₂
    obtain ⟨s, -, rfl⟩ := mem_image.mp hc₁
    obtain ⟨t, -, het⟩ := mem_image.mp hc₂
    exact hdisj s t (wignerCoord_eq_iff.mp het.symm)
  have hX (k : StrictUpper ⊕ ℕ) : AEMeasurable (X k) P := aemeasurable_sumElim_ofReal hξm hηm k
  let c : ℂ := (Real.sqrt n : ℂ)⁻¹
  let φ₁ : (S₁ → ℂ) → ℂ := fun g ↦
    ∏ s : ι₁, c * wignerOrient (u₁ s) (v₁ s) (g ⟨e₁ s, mem_image_of_mem e₁ (mem_univ s)⟩)
  let φ₂ : (S₂ → ℂ) → ℂ := fun g ↦
    ∏ t : ι₂, c * wignerOrient (u₂ t) (v₂ t) (g ⟨e₂ t, mem_image_of_mem e₂ (mem_univ t)⟩)
  have hφ₁ : Measurable φ₁ := Finset.measurable_prod _ fun s _ ↦
    measurable_const.mul ((measurable_wignerOrient _ _).comp (measurable_pi_apply _))
  have hφ₂ : Measurable φ₂ := Finset.measurable_prod _ fun t _ ↦
    measurable_const.mul ((measurable_wignerOrient _ _).comp (measurable_pi_apply _))
  have hXS₁ : AEMeasurable (fun ω (k : S₁) ↦ X k ω) P := aemeasurable_pi_iff.2 fun k ↦ hX k
  have hXS₂ : AEMeasurable (fun ω (k : S₂) ↦ X k ω) P := aemeasurable_pi_iff.2 fun k ↦ hX k
  have hind := (hindep.indepFun_finset₀ S₁ S₂ hS₁₂ hX).comp hφ₁ hφ₂
  have heq₁ (ω : Ω) : (∏ s, wignerMatrix ξ η n ω (u₁ s) (v₁ s)) = φ₁ (fun k : S₁ ↦ X k ω) := by
    simp only [wignerMatrix_apply_eq_wignerOrient, φ₁, X, e₁, c]
  have heq₂ (ω : Ω) : (∏ t, wignerMatrix ξ η n ω (u₂ t) (v₂ t)) = φ₂ (fun k : S₂ ↦ X k ω) := by
    simp only [wignerMatrix_apply_eq_wignerOrient, φ₂, X, e₂, c]
  simp_rw [heq₁, heq₂]
  have hmul := hind.integral_fun_mul_eq_mul_integral
    (hφ₁.comp_aemeasurable hXS₁).aestronglyMeasurable
    (hφ₂.comp_aemeasurable hXS₂).aestronglyMeasurable
  simpa only [Function.comp_apply] using hmul

/-- A product of `k` Wigner entries lies in `L²` when the underlying array entries lie in
`L^{2k}`. -/
theorem memLp_two_prod_wignerMatrix_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {ι : Type*} [Fintype ι]
    (hξ : ∀ ij, MemLp (ξ ij) (2 * Fintype.card ι : ℕ) P)
    (hη : ∀ i, MemLp (η i) (2 * Fintype.card ι : ℕ) P)
    {n : ℕ} (u v : ι → Fin n) :
    MemLp (fun ω ↦ ∏ s, wignerMatrix ξ η n ω (u s) (v s)) 2 P := by
  cases isEmpty_or_nonempty ι
  · simpa using memLp_const (1 : ℂ)
  · have hcard : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
    have h := MemLp.fun_prod (s := Finset.univ)
      (p := fun _ : ι ↦ ((2 * Fintype.card ι : ℕ) : ℝ≥0∞))
      fun s _ ↦ memLp_wignerMatrix_apply hξ hη (u s) (v s)
    have hexp : ∑ _s : ι, (((2 * Fintype.card ι : ℕ) : ℝ≥0∞))⁻¹ = 2⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
        mul_left_comm (Fintype.card ι : ℝ≥0∞) (2 : ℝ≥0∞)⁻¹ _,
        ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _), mul_one]
    rwa [hexp, inv_inv] at h

/-- The `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)` lies in `L²` when the array
entries lie in `L^{2k}`. -/
theorem memLp_two_integral_pow_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k : ℕ}
    (hξ : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hη : ∀ i, MemLp (η i) (2 * k : ℕ) P) (n : ℕ) :
    MemLp (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) 2 P := by
  have hZ : MemLp (fun ω ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace) 2 P := by
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using (memLp_const ((n + 1 : ℕ) : ℂ)).const_mul _
    · simp_rw [trace_pow_eq_sum_prod _ hk]
      have hξ' : ∀ ij, MemLp (ξ ij) (2 * Fintype.card (Fin k) : ℕ) P := by
        rwa [Fintype.card_fin]
      have hη' : ∀ i, MemLp (η i) (2 * Fintype.card (Fin k) : ℕ) P := by
        rwa [Fintype.card_fin]
      have hsum : MemLp (fun ω ↦ ∑ w : Fin k → Fin (n + 1),
          ∏ t, wignerMatrix ξ η (n + 1) ω (w t) (w (finRotate k t))) 2 P :=
        memLp_finsetSum (univ : Finset (Fin k → Fin (n + 1))) fun w _ ↦
          memLp_two_prod_wignerMatrix_apply hξ' hη' w (w ∘ finRotate k)
      exact hsum.const_mul _
  simpa only [Function.comp_def, Complex.reCLM_apply,
    inv_mul_trace_pow_wignerMatrix_eq_ofReal_integral, Complex.ofReal_re] using
    Complex.reCLM.comp_memLp' hZ

private theorem prod_mul_star_prod_wignerMatrix_apply_eq {Ω : Type*}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} (ω : Ω)
    (w₁ w₂ : Fin k → Fin n) :
    (∏ s, wignerMatrix ξ η n ω (w₁ s) (w₁ (finRotate k s))) *
        star (∏ t, wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t))) =
      ∏ x : Fin k ⊕ Fin k, wignerMatrix ξ η n ω
        (Sum.elim w₁ (w₂ ∘ finRotate k) x)
        (Sum.elim (w₁ ∘ finRotate k) w₂ x) := by
  have hstar (t : Fin k) :
      star (wignerMatrix ξ η n ω (w₂ t) (w₂ (finRotate k t))) =
        wignerMatrix ξ η n ω (w₂ (finRotate k t)) (w₂ t) := by
    simpa only [conjTranspose_apply] using
      (wignerMatrix_isHermitian ξ η ω n).apply (w₂ (finRotate k t)) (w₂ t)
  rw [star_prod, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, hstar]

private theorem norm_integral_prod_mul_star_prod_wignerMatrix_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w₁ w₂ : Fin k → Fin (n + 1)) :
    ‖∫ ω, (∏ s, wignerMatrix ξ η (n + 1) ω (w₁ s) (w₁ (finRotate k s))) *
        star (∏ t, wignerMatrix ξ η (n + 1) ω (w₂ t) (w₂ (finRotate k t))) ∂P‖ ≤
      (n + 1 : ℝ)⁻¹ ^ k * B := by
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  simp_rw [prod_mul_star_prod_wignerMatrix_apply_eq]
  have h := norm_integral_prod_wignerMatrix_apply_le (ι := Fin k ⊕ Fin k)
    (by simpa [hcard] using hξp) (by simpa [hcard] using hηp)
    (by simpa [hcard] using hξ) (by simpa [hcard] using hη)
    (Sum.elim w₁ (w₂ ∘ finRotate k)) (Sum.elim (w₁ ∘ finRotate k) w₂)
  have hs : (Real.sqrt (n + 1 : ℕ))⁻¹ ^ (2 * k) = (n + 1 : ℝ)⁻¹ ^ k := by
    rw [inv_pow, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _), inv_pow, Nat.cast_add, Nat.cast_one]
  rwa [hcard, hs] at h

private theorem norm_integral_prod_wignerMatrix_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} {B : ℝ}
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    (w : Fin k → Fin (n + 1)) :
    ‖∫ ω, ∏ s, wignerMatrix ξ η (n + 1) ω (w s) (w (finRotate k s)) ∂P‖ ^ 2 ≤
      (n + 1 : ℝ)⁻¹ ^ k * B := by
  let T : Ω → ℂ := fun ω ↦ ∏ s, wignerMatrix ξ η (n + 1) ω (w s) (w (finRotate k s))
  have hT2 : MemLp (fun ω ↦ ‖T ω‖) 2 P :=
    (memLp_two_prod_wignerMatrix_apply (by simpa using hξp) (by simpa using hηp)
      w (w ∘ finRotate k)).norm
  have hcs : (∫ ω, ‖T ω‖ ∂P) ^ 2 ≤ ∫ ω, ‖T ω‖ ^ 2 ∂P := by
    have hvar := variance_nonneg (fun ω ↦ ‖T ω‖) P
    rw [variance_eq_sub hT2] at hvar
    simpa only [Pi.pow_apply] using sub_nonneg.mp hvar
  have hni : ‖∫ ω, T ω ∂P‖ ^ 2 ≤ (∫ ω, ‖T ω‖ ∂P) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm T) 2
  have hsq : ∫ ω, ‖T ω‖ ^ 2 ∂P = ‖∫ ω, T ω * star (T ω) ∂P‖ := by
    have hnn : 0 ≤ ∫ ω, ‖T ω‖ ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
    have hmul (ω : Ω) : T ω * star (T ω) = ((‖T ω‖ ^ 2 : ℝ) : ℂ) := by
      simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (T ω)
    simp_rw [hmul, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnn]
  exact (hni.trans hcs).trans (hsq ▸
    norm_integral_prod_mul_star_prod_wignerMatrix_le hξp hηp hξ hη w w)

private theorem ofReal_sq_eq_mul_sum_mul_star {ι : Type*} [Fintype ι] {r : ℝ} {c : ℂ}
    (hc : star c = c) {g : ι → ℂ} (hr : (r : ℂ) = c * ∑ i, g i) :
    ((r ^ 2 : ℝ) : ℂ) = c ^ 2 * ∑ p : ι × ι, g p.1 * star (g p.2) := by
  calc
    ((r ^ 2 : ℝ) : ℂ) = (r : ℂ) * star (r : ℂ) := by simp [sq]
    _ = (c * ∑ i, g i) * (star c * ∑ j, star (g j)) := by rw [hr, star_mul', star_sum]
    _ = c ^ 2 * ((∑ i, g i) * ∑ j, star (g j)) := by rw [hc]; ring
    _ = c ^ 2 * ∑ p : ι × ι, g p.1 * star (g p.2) := by rw [Fintype.sum_prod_type, sum_mul_sum]

/-- **Variance bound for Wigner empirical spectral moments** (Anderson–Guionnet–Zeitouni,
Lemma 2.1.7). For independent centered array entries with `2 * k`th absolute moments bounded by `B`,
the variance of the `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)` is at most
`2 * k ^ (2 * k) * B / (n + 1) ^ 2`. No identical distribution or second-moment normalization is
required. -/
theorem variance_integral_pow_spectralMeasure_wignerMatrix_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    Var[fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hB : 0 ≤ B := (integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg (η 0 ω)) _).trans (hη 0)
  rcases eq_or_ne k 0 with rfl | hk
  · have hconst : (fun ω ↦ ∫ x, x ^ 0 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) = fun _ ↦ 1 := by
      ext ω
      simp
    rw [hconst, variance_eq_sub (memLp_const 1)]
    simp only [Pi.pow_apply, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one,
      sub_self]
    positivity
  · let X : Ω → ℝ := fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)
    let T (w : Fin k → Fin (n + 1)) (ω : Ω) : ℂ :=
      ∏ s, wignerMatrix ξ η (n + 1) ω (w s) (w (finRotate k s))
    let covTerm (p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1))) : ℂ :=
      (∫ ω, T p.1 ω * star (T p.2 ω) ∂P) -
        (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P)
    have hX2 : MemLp X 2 P := memLp_two_integral_pow_spectralMeasure_wignerMatrix hξp hηp n
    have hξpk (ij : StrictUpper) : MemLp (ξ ij) (k : ℕ) P :=
      (hξp ij).mono_exponent (by norm_cast; omega)
    have hηpk (i : ℕ) : MemLp (η i) (k : ℕ) P :=
      (hηp i).mono_exponent (by norm_cast; omega)
    have hξm (ij : StrictUpper) : AEMeasurable (ξ ij) P := (hξpk ij).aemeasurable
    have hηm (i : ℕ) : AEMeasurable (η i) P := (hηpk i).aemeasurable
    have hintT (w : Fin k → Fin (n + 1)) : Integrable (T w) P :=
      integrable_prod_wignerMatrix_apply (by simpa using hξpk) (by simpa using hηpk)
        w (w ∘ finRotate k)
    have hintTT (w₁ w₂ : Fin k → Fin (n + 1)) :
        Integrable (fun ω ↦ T w₁ ω * star (T w₂ ω)) P := by
      have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
        rw [Fintype.card_sum, Fintype.card_fin, two_mul]
      simp_rw [T, prod_mul_star_prod_wignerMatrix_apply_eq]
      exact integrable_prod_wignerMatrix_apply
        (by simpa [hcard] using hξp) (by simpa [hcard] using hηp) _ _
    have hXeq (ω : Ω) : ((X ω : ℝ) : ℂ) =
        ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ w : Fin k → Fin (n + 1), T w ω := by
      rw [← inv_mul_trace_pow_wignerMatrix_eq_ofReal_integral n k ω, trace_pow_eq_sum_prod _ hk]
    have hmeanC : ((∫ ω, X ω ∂P : ℝ) : ℂ) =
        ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ w : Fin k → Fin (n + 1), ∫ ω, T w ω ∂P := by
      rw [← integral_complex_ofReal]
      simp_rw [hXeq]
      rw [integral_const_mul, integral_finsetSum _ fun w _ ↦ hintT w]
    have hsqC : ((∫ ω, X ω ^ 2 ∂P : ℝ) : ℂ) =
        ((n + 1 : ℕ) : ℂ)⁻¹ ^ 2 *
          ∑ p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1)),
            ∫ ω, T p.1 ω * star (T p.2 ω) ∂P := by
      rw [← integral_complex_ofReal]
      simp_rw [fun ω ↦ ofReal_sq_eq_mul_sum_mul_star (by simp) (hXeq ω)]
      rw [integral_const_mul, integral_finsetSum _ fun p _ ↦ hintTT p.1 p.2]
    have hvarC : ((Var[X; P] : ℝ) : ℂ) =
        ((n + 1 : ℕ) : ℂ)⁻¹ ^ 2 *
          ∑ p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1)), covTerm p := by
      rw [variance_eq_sub hX2]
      simp only [Pi.pow_apply, Complex.ofReal_sub]
      rw [hsqC, ofReal_sq_eq_mul_sum_mul_star (by simp) hmeanC,
        ← mul_sub, ← Finset.sum_sub_distrib]
    let G : Finset ((Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1))) :=
      {p | (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))) ∧
        ∀ x : Fin k ⊕ Fin k, ∃ y ≠ x,
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k t))) y =
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k t))) x}
    have hsumG : (∑ p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1)), covTerm p) =
        ∑ p ∈ G, covTerm p := by
      symm
      refine Finset.sum_subset (Finset.subset_univ G) fun p _ hpG ↦ ?_
      simp only [G, mem_filter, mem_univ, true_and, not_and] at hpG
      by_cases hshare : ∃ t₁ t₂,
          s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))
      · obtain ⟨x₀, hx₀⟩ := not_forall.mp (hpG hshare)
        have hedges (y : Fin k ⊕ Fin k) :
            s(Sum.elim p.1 (p.2 ∘ finRotate k) y, Sum.elim (p.1 ∘ finRotate k) p.2 y) =
              Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
                (fun t ↦ s(p.2 t, p.2 (finRotate k t))) y := by
          cases y <;> simp [Sym2.eq_swap]
        have hzero1 : ∫ ω, T p.1 ω * star (T p.2 ω) ∂P = 0 := by
          simp_rw [T, prod_mul_star_prod_wignerMatrix_apply_eq]
          exact integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero
            (Sum.elim p.1 (p.2 ∘ finRotate k)) (Sum.elim (p.1 ∘ finRotate k) p.2)
            (t := x₀) fun y hy ↦ by
              by_contra hne
              exact hx₀ ⟨y, hne, by rwa [← hedges y, ← hedges x₀]⟩
        have hzero2 : (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P) = 0 := by
          cases x₀ with
          | inl s₀ =>
            have hz : ∫ ω, T p.1 ω ∂P = 0 :=
              integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero
                p.1 (p.1 ∘ finRotate k) (t := s₀) fun s hs ↦ by
                  by_contra hne
                  exact hx₀ ⟨.inl s, Sum.inl_injective.ne hne, by simpa using hs⟩
            simp [hz]
          | inr t₀ =>
            have hz : ∫ ω, T p.2 ω ∂P = 0 :=
              integral_prod_wignerMatrix_apply_eq_zero hξm hηm hindep hξzero hηzero
                p.2 (p.2 ∘ finRotate k) (t := t₀) fun t ht ↦ by
                  by_contra hne
                  exact hx₀ ⟨.inr t, Sum.inr_injective.ne hne, by simpa using ht⟩
            simp [hz]
        dsimp only [covTerm]
        rw [hzero1, hzero2, sub_zero]
      · have hdisj (s t : Fin k) :
            s(p.1 s, p.1 (finRotate k s)) ≠ s(p.2 (finRotate k t), p.2 t) := by
          rw [Sym2.eq_swap (a := p.2 (finRotate k t))]
          exact fun h ↦ hshare ⟨s, t, h⟩
        have hstarT (ω : Ω) : star (T p.2 ω) =
            ∏ t, wignerMatrix ξ η (n + 1) ω (p.2 (finRotate k t)) (p.2 t) := by
          have hstar (t : Fin k) :
              star (wignerMatrix ξ η (n + 1) ω (p.2 t) (p.2 (finRotate k t))) =
                wignerMatrix ξ η (n + 1) ω (p.2 (finRotate k t)) (p.2 t) := by
            simpa only [conjTranspose_apply] using
              (wignerMatrix_isHermitian ξ η ω (n + 1)).apply (p.2 (finRotate k t)) (p.2 t)
          dsimp only [T]
          rw [star_prod]
          exact Finset.prod_congr rfl fun t _ ↦ hstar t
        have hfact : ∫ ω, T p.1 ω * star (T p.2 ω) ∂P =
            (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P) := by
          have hmul := integral_prod_mul_prod_wignerMatrix_apply_eq_mul_integral hξm hηm hindep
            p.1 (p.1 ∘ finRotate k) (p.2 ∘ finRotate k) p.2 hdisj
          simp only [Function.comp_apply] at hmul
          calc
            ∫ ω, T p.1 ω * star (T p.2 ω) ∂P
              = ∫ ω, (∏ s, wignerMatrix ξ η (n + 1) ω (p.1 s) (p.1 (finRotate k s))) *
                  (∏ t, wignerMatrix ξ η (n + 1) ω (p.2 (finRotate k t)) (p.2 t)) ∂P := by
                simp_rw [hstarT]
                rfl
            _ = (∫ ω, T p.1 ω ∂P) *
                  ∫ ω, ∏ t, wignerMatrix ξ η (n + 1) ω (p.2 (finRotate k t)) (p.2 t) ∂P := hmul
            _ = (∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P) := by
                congr 1
                simp_rw [← hstarT]
                exact integral_conj
        exact sub_eq_zero.mpr hfact
    have hcov_le (p : (Fin k → Fin (n + 1)) × (Fin k → Fin (n + 1))) :
        ‖covTerm p‖ ≤ 2 * (n + 1 : ℝ)⁻¹ ^ k * B := by
      have h1 := norm_integral_prod_mul_star_prod_wignerMatrix_le hξp hηp hξ hη p.1 p.2
      have h2₁ := norm_integral_prod_wignerMatrix_sq_le hξp hηp hξ hη p.1
      have h2₂ := norm_integral_prod_wignerMatrix_sq_le hξp hηp hξ hη p.2
      have hprod : ‖(∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P)‖ ≤ (n + 1 : ℝ)⁻¹ ^ k * B := by
        rw [norm_mul, norm_star]
        have hsq_mul : (‖∫ ω, T p.1 ω ∂P‖ * ‖∫ ω, T p.2 ω ∂P‖) ^ 2 ≤
            ((n + 1 : ℝ)⁻¹ ^ k * B) ^ 2 := by
          rw [mul_pow, sq ((n + 1 : ℝ)⁻¹ ^ k * B)]
          exact mul_le_mul h2₁ h2₂ (sq_nonneg _) (mul_nonneg (by positivity) hB)
        exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (by positivity) hB)
          (by simpa only [sq] using hsq_mul)
      calc
        ‖covTerm p‖ ≤ ‖∫ ω, T p.1 ω * star (T p.2 ω) ∂P‖ +
            ‖(∫ ω, T p.1 ω ∂P) * star (∫ ω, T p.2 ω ∂P)‖ := norm_sub_le _ _
        _ ≤ (n + 1 : ℝ)⁻¹ ^ k * B + (n + 1 : ℝ)⁻¹ ^ k * B := add_le_add h1 hprod
        _ = 2 * (n + 1 : ℝ)⁻¹ ^ k * B := by ring
    have hGcard : (#G : ℝ) ≤ (n + 1 : ℝ) ^ k * (k : ℝ) ^ (2 * k) := by
      have hc := TreeWalk.card_filter_connectedPair_le (α := Fin (n + 1)) k
      simp only [Fintype.card_fin] at hc
      exact_mod_cast hc
    have hvar_norm : Var[X; P] = ‖((Var[X; P] : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (variance_nonneg X P)]
    have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hcancel : (n + 1 : ℝ) ^ k * (n + 1 : ℝ)⁻¹ ^ k = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hn0, one_pow]
    rw [hvar_norm, hvarC, hsumG, norm_mul, norm_pow, norm_inv, Complex.norm_natCast,
      Nat.cast_add, Nat.cast_one]
    calc
      (n + 1 : ℝ)⁻¹ ^ 2 * ‖∑ p ∈ G, covTerm p‖
        ≤ (n + 1 : ℝ)⁻¹ ^ 2 * ∑ p ∈ G, ‖covTerm p‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le G covTerm) (by positivity)
      _ ≤ (n + 1 : ℝ)⁻¹ ^ 2 * ∑ _p ∈ G, (2 * (n + 1 : ℝ)⁻¹ ^ k * B) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ ↦ hcov_le p) (by positivity)
      _ = (n + 1 : ℝ)⁻¹ ^ 2 * ((#G : ℝ) * (2 * (n + 1 : ℝ)⁻¹ ^ k * B)) := by simp
      _ ≤ (n + 1 : ℝ)⁻¹ ^ 2 *
            (((n + 1 : ℝ) ^ k * (k : ℝ) ^ (2 * k)) * (2 * (n + 1 : ℝ)⁻¹ ^ k * B)) := by
          gcongr
      _ = ((n + 1 : ℝ) ^ k * (n + 1 : ℝ)⁻¹ ^ k) *
            (2 * (k : ℝ) ^ (2 * k) * B * (n + 1 : ℝ)⁻¹ ^ 2) := by ring
      _ = 2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2 := by
          rw [hcancel, one_mul, div_eq_mul_inv, inv_pow]

/-- Chebyshev's tail bound for the `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)`
around its expectation. -/
theorem measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k n : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian ξ η ω' (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hmem := memLp_two_integral_pow_spectralMeasure_wignerMatrix hξp hηp n
  refine (meas_ge_le_variance_div_sq hmem hε).trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right
    (variance_integral_pow_spectralMeasure_wignerMatrix_le
      hindep hξzero hηzero hξp hηp hξ hη)
    (sq_nonneg ε)

/-- Fluctuations of the `k`th empirical spectral moment around its expectation vanish in
probability, including on varying probability spaces. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
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
  have hreal : Tendsto (fun n : ℕ ↦
      (2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2) atTop (𝓝 0) := by
    convert ((hinv.pow 2).const_mul (2 * (k : ℝ) ^ (2 * k) * B)).div_const (ε ^ 2) using 1
    · ext n
      simp [div_eq_mul_inv, inv_pow]
    · simp
  have hbound : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ε ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ bot_le) fun n ↦
      measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
        (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n) hε

private theorem integral_norm_pow_le_one_add {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → E}
    {k : ℕ} {B : ℝ} (hfp : MemLp f (2 * k : ℕ) P) (hf : ∫ ω, ‖f ω‖ ^ (2 * k) ∂P ≤ B) :
    ∫ ω, ‖f ω‖ ^ k ∂P ≤ 1 + B := by
  have hfk : MemLp f (k : ℕ) P := hfp.mono_exponent (by norm_cast; omega)
  calc
    ∫ ω, ‖f ω‖ ^ k ∂P
      ≤ ∫ ω, (1 + ‖f ω‖ ^ (2 * k)) ∂P :=
        integral_mono hfk.integrable_norm_pow'
          ((integrable_const 1).add hfp.integrable_norm_pow')
          fun ω ↦ pow_le_one_add_pow_two_mul _ (norm_nonneg _) k
    _ = 1 + ∫ ω, ‖f ω‖ ^ (2 * k) ∂P := by
        rw [integral_add (integrable_const 1) hfp.integrable_norm_pow', integral_const]
        simp
    _ ≤ 1 + B := add_le_add_right hf 1

/-- For Wigner matrices on (possibly varying) probability spaces with independent centered entries,
unit off-diagonal second moments, and uniformly bounded `2 * k`th absolute moments, the `k`th
empirical spectral moment converges in probability to the `k`th moment of `semicircleReal 0 1`. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P n ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ x, x ^ k ∂semicircleReal 0 1|}) atTop (𝓝 0) := by
  have hprob (n : ℕ) : IsProbabilityMeasure (P n) := (hindep n).isProbabilityMeasure
  have hmean := tendsto_integral_pow_spectralMeasure_wignerMatrix
    hindep hξzero hηzero hsecond
    (fun n ij ↦ (hξp n ij).mono_exponent (by norm_cast; omega))
    (fun n i ↦ (hηp n i).mono_exponent (by norm_cast; omega))
    (fun n ij ↦ integral_norm_pow_le_one_add (hξp n ij) (hξ n ij))
    (fun n i ↦ integral_norm_pow_le_one_add (hηp n i) (hη n i))
  have hfluc := tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean_probability
    hindep hξzero hηzero hξp hηp hξ hη (half_pos hε)
  have hev : ∀ᶠ n in atTop,
      P n {ω | ε ≤
        |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
        ∫ x, x ^ k ∂semicircleReal 0 1|} ≤
      P n {ω | ε / 2 ≤
        |(∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
        ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
          (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n|} := by
    filter_upwards [Metric.tendsto_nhds.1 hmean (ε / 2) (half_pos hε)] with n hn
    rw [Real.dist_eq] at hn
    refine measure_mono fun ω hω ↦ ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith [abs_sub_le
      (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      (∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P n)
      (∫ x, x ^ k ∂semicircleReal 0 1)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfluc
    (Eventually.of_forall fun _ ↦ bot_le) hev

/-- Fluctuations of the `k`th empirical spectral moment around its expectation tend almost surely to
zero for any sequence of Wigner arrays on `(Ω, P)` with independent centered entries at each matrix
size and uniformly bounded `2 * k`th absolute moments. No independence across different matrix sizes
is required. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) P)
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hindep 0).isProbabilityMeasure
  let Y : ℕ → Ω → ℝ := fun n ω ↦
    (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
    ∫ ω', (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω').spectralMeasure
      (wignerMatrix_isHermitian (ξ n) (η n) ω' (n + 1)) : Measure ℝ)) ∂P
  have hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, inv_pow] using
      (summable_nat_add_iff 1).2 ((Real.summable_nat_pow_inv (p := 2)).2 (by decide : 1 < 2))
  have hbc (m : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |Y n ω| < (m + 1 : ℝ)⁻¹ := by
    have hbound (n : ℕ) : P {ω | (m + 1 : ℝ)⁻¹ ≤ |Y n ω|} ≤
        ENNReal.ofReal
          ((2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) :=
      measure_integral_pow_spectralMeasure_wignerMatrix_sub_mean_ge
        (hindep n) (hξzero n) (hηzero n) (hξp n) (hηp n) (hξ n) (hη n)
        (inv_pos.mpr (by positivity))
    have hsum : Summable (fun n : ℕ ↦
        (2 * (k : ℝ) ^ (2 * k) * B / (n + 1 : ℝ) ^ 2) / ((m + 1 : ℝ)⁻¹) ^ 2) := by
      have ht := Summable.mul_right ((((m + 1 : ℝ)⁻¹) ^ 2)⁻¹)
        (Summable.mul_left (2 * (k : ℝ) ^ (2 * k) * B) hs)
      simpa only [div_eq_mul_inv, inv_pow, mul_assoc] using ht
    have hfinite : (∑' n, P {ω | (m + 1 : ℝ)⁻¹ ≤ |Y n ω|}) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum hbound)
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfinite
  -- Intersect the full-measure Borel–Cantelli events over tolerances `(m + 1)⁻¹ → 0`.
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω m] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn.trans (by simpa only [one_div] using hm)

/-- Almost-sure convergence of the `k`th empirical spectral moment to the `k`th moment of
`semicircleReal 0 1` for any sequence of Wigner arrays `(ξ n, η n)` on `(Ω, P)` with independent
centered entries at each size, unit off-diagonal second moments, and uniformly bounded `2 * k`th
absolute moments. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : ℕ → StrictUpper → Ω → ℂ} {η : ℕ → ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun
      (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) r) P)
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P = 0)
    (hηzero : ∀ n i, ∫ ω, η n i ω ∂P = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * k : ℕ) P)
    (hηp : ∀ n i, MemLp (η n i) (2 * k : ℕ) P)
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have : IsProbabilityMeasure P := (hindep 0).isProbabilityMeasure
  have hmean := tendsto_integral_pow_spectralMeasure_wignerMatrix
    (P := fun _ ↦ P) hindep hξzero hηzero hsecond
    (fun n ij ↦ (hξp n ij).mono_exponent (by norm_cast; omega))
    (fun n i ↦ (hηp n i).mono_exponent (by norm_cast; omega))
    (fun n ij ↦ integral_norm_pow_le_one_add (hξp n ij) (hξ n ij))
    (fun n i ↦ integral_norm_pow_le_one_add (hηp n i) (hη n i))
  filter_upwards [ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_sub_mean
    hindep hξzero hηzero hξp hηp hξ hη] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add hmean

/-- Almost-sure convergence of the `k`th empirical spectral moment to the `k`th moment of
`semicircleReal 0 1` for the corners of a single infinite Wigner array `(ξ, η)` with independent
centered entries, unit off-diagonal second moments, and uniformly bounded `2 * k`th absolute
moments. -/
theorem ae_tendsto_integral_pow_spectralMeasure_wignerMatrix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun r : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) r) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * k : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * k : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * k) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * k) ∂P ≤ B) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ))
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) :=
  ae_tendsto_integral_pow_spectralMeasure_wignerMatrix_of_seq
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hηzero) (fun _ ↦ hsecond)
    (fun _ ↦ hξp) (fun _ ↦ hηp) (fun _ ↦ hξ) (fun _ ↦ hη)

end VarianceAndConcentration

end TauCeti.Probability
