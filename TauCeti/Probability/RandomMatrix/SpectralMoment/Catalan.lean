/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Combinatorics.TreeWalk.Enumeration
public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.RandomMatrix.MomentBounds
import TauCeti.Data.Nat.Factorial.Basic

/-!
# Convergence of expected Wigner spectral moments to the semicircle moments

Combining the exact enumeration of leading cyclic words (`card_filter_leadingCyclicWords`) with the
entry-product evaluation (`integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one`)
and remainder bound (`norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le`)
identifies the `O(1/n)` asymptotic of every even normalized expected trace of a Wigner matrix:
for every `m : ℕ` and `n ≠ 0`,
`‖n⁻¹ * E[tr(Hₙ ^ (2m))] - catalan m‖ ≤ (m ^ (2m) * B + catalan m * (m + 1).choose 2) / n`.

Because `Hₙ` is Hermitian, `(Hₙ ^ k).trace` is real and `n⁻¹ * (Hₙ ^ k).trace` equals the `k`-th
moment of the empirical spectral measure. Together with the `O(n ^ (-1/2))` bound on odd moments
and the semicircle moment formulas (`integral_pow_two_mul_semicircleReal_zero` and
`integral_pow_two_mul_add_one_semicircleReal_zero`), every expected empirical spectral moment of a
Wigner matrix (or triangular Wigner array) converges to the corresponding moment of the standard
semicircle distribution `semicircleReal 0 1`.

## Main results

* `TauCeti.sum_integral_prod_wignerMatrix_leading`: the leading words of length `2 * m` (`m ≠ 0`)
  contribute `(catalan m * n.descFactorial (m + 1)) * n⁻¹ ^ m` to the expected trace.
* `TauCeti.norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le`: quantitative
  `O(1 / n)` rate of convergence of the normalized expected `2m`-th trace to `catalan m`.
* `TauCeti.tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix`: convergence of the normalized
  expected `2m`-th trace to `catalan m` for all `m : ℕ`.
* `TauCeti.Probability.tendsto_integral_spectralMoment_wignerMatrix_array`,
  `TauCeti.Probability.tendsto_integral_spectralMoment_wignerMatrix`: convergence of expected
  `k`-th empirical spectral moments to `∫ x, x ^ k ∂semicircleReal 0 1` for all `k : ℕ`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter TauCeti.TreeWalk
open scoped Topology

namespace TauCeti

private theorem norm_catalan_mul_descFactorial_inv_pow_sub_le {m n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℂ)⁻¹ * ((catalan m * n.descFactorial (m + 1) : ℂ) * (n : ℂ)⁻¹ ^ m) - (catalan m : ℂ)‖ ≤
      (catalan m * (m + 1).choose 2 : ℝ) / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpowR : (0 : ℝ) < (n : ℝ) ^ (m + 1) := pow_pos hnR _
  have hdf_le : (n.descFactorial (m + 1) : ℝ) ≤ (n : ℝ) ^ (m + 1) := by
    exact_mod_cast Nat.descFactorial_le_pow n (m + 1)
  have hsub_le : (n : ℝ) ^ (m + 1) - n.descFactorial (m + 1) ≤
      (m + 1).choose 2 * (n : ℝ) ^ m := by
    have h := Nat.pow_succ_le_descFactorial_add_choose_two_mul_pow n m
    have hR : ((n : ℝ) ^ (m + 1)) ≤ n.descFactorial (m + 1) + (m + 1).choose 2 * (n : ℝ) ^ m := by
      exact_mod_cast h
    linarith
  have hcast :
      (n : ℂ)⁻¹ * ((catalan m * n.descFactorial (m + 1) : ℂ) * (n : ℂ)⁻¹ ^ m) - (catalan m : ℂ) =
        (((catalan m : ℝ) * ((n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) - 1) : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv, inv_pow]
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonpos (by linarith [(div_le_one hpowR).mpr hdf_le]), neg_sub]
  have hdiv : 1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) ≤
      ((m + 1).choose 2 : ℝ) / n := by
    rw [one_sub_div hpowR.ne']
    calc
      ((n : ℝ) ^ (m + 1) - n.descFactorial (m + 1)) / (n : ℝ) ^ (m + 1)
        ≤ ((m + 1).choose 2 * (n : ℝ) ^ m) / (n : ℝ) ^ (m + 1) :=
          div_le_div_of_nonneg_right hsub_le hpowR.le
      _ = ((m + 1).choose 2 : ℝ) / n := by rw [pow_succ]; field_simp
  calc
    (catalan m : ℝ) * (1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1))
      ≤ (catalan m : ℝ) * (((m + 1).choose 2 : ℝ) / n) :=
        mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
    _ = (catalan m * (m + 1).choose 2 : ℝ) / n := by ring

section TraceMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- Because `wignerMatrix` is Hermitian, the trace of any natural power is real. -/
theorem ofReal_re_trace_pow_wignerMatrix (n k : ℕ) (ω : Ω) :
    (((wignerMatrix ξ η n ω ^ k).trace).re : ℂ) = (wignerMatrix ξ η n ω ^ k).trace := by
  rw [(wignerMatrix_isHermitian ξ η ω n).trace_pow_eq_sum_eigenvalues_pow k,
    Complex.re_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- On a finite measure space, the trace of the `k`-th power of a Wigner matrix is integrable
whenever all coordinates belong to `Lᵏ`. -/
theorem integrable_trace_pow_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P) (n : ℕ) :
    Integrable (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [pow_zero, trace_one, Fintype.card_fin]
    exact integrable_const _
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    exact integrable_finsetSum _ fun w _ ↦
      integrable_prod_wignerMatrix_apply (by simpa using hξp) (by simpa using hηp) _ _

/-- **Leading trace-word sum.** For `m ≠ 0`, independent upper-triangular entries with unit second
absolute moments give exact leading-word sum `(catalan m * n.descFactorial (m + 1)) * n⁻¹ ^ m`. -/
theorem sum_integral_prod_wignerMatrix_leading {m n : ℕ} (hm : m ≠ 0)
    (hindep : iIndepFun ξ P) (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1) :
    (∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) =
      (catalan m * n.descFactorial (m + 1) : ℂ) * (n : ℂ)⁻¹ ^ m := by
  have : NeZero m := ⟨hm⟩
  rw [sum_congr rfl fun w hw ↦
    integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one hindep hsecond w
      (mem_filter.mp hw).2.1 (mem_filter.mp hw).2.2]
  rw [sum_const, card_filter_leadingCyclicWords, Fintype.card_fin]
  simp [nsmul_eq_mul]

private theorem norm_inv_mul_integral_trace_pow_two_mul_sub_leading_le {m n : ℕ} (hm : m ≠ 0)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P)‖ ≤
      (m : ℝ) ^ (2 * m) * B / n := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  let S : Finset (Fin (2 * m) → Fin n) := {w | ∀ t, w t ≠ w (finRotate (2 * m) t) →
    ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))}
  let F (w : Fin (2 * m) → Fin n) :=
    ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P
  have hlead_eq : S.filter (fun w ↦ #(univ.image w) = m + 1) =
      univ.filter fun w ↦
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1 := by
    ext w
    simp only [S, mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨hnl, hv⟩ ↦
      ⟨(no_singleton_edge_of_no_singleton_nonloop_edge_of_card_image_eq w hnl hv).2, hv⟩,
      fun ⟨hall, hv⟩ ↦ ⟨fun t _ ↦ hall t, hv⟩⟩
  have hsplit : (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w ∈ S with #(univ.image w) = m + 1, F w =
        ∑ w ∈ S with #(univ.image w) ≠ m + 1, F w := by
    rw [integral_trace_pow_wignerMatrix_of_ne hindep hξzero (by omega) hξp hηp]
    exact sub_eq_iff_eq_add.mpr
      (by simpa only [S, F, add_comm] using
        (sum_filter_add_sum_filter_not S (fun w ↦ #(univ.image w) = m + 1) F).symm)
  have hbound := norm_sum_integral_prod_wignerMatrix_le (n := n) (r := m)
    (by omega) hξp hηp hξ hη (S.filter fun w ↦ #(univ.image w) ≠ m + 1) fun w hw ↦ by
      obtain ⟨hwS, hwne⟩ := mem_filter.mp hw
      have hv := card_image_le_div_two_add_one_of_no_singleton_nonloop_edge w (mem_filter.mp hwS).2
      omega
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m) = (n : ℝ) ^ m := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← hlead_eq, hsplit, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((m : ℝ) ^ (2 * m) * (n : ℝ) ^ m * (Real.sqrt n)⁻¹ ^ (2 * m) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; field_simp

private theorem norm_inv_mul_integral_trace_pow_two_mul_add_one_of_ne_le (m n : ℕ)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m + 1)).trace ∂P‖ ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  let S : Finset (Fin (2 * m + 1) → Fin n) := {w | ∀ t, w t ≠ w (finRotate (2 * m + 1) t) →
    ∃ s ≠ t, s(w s, w (finRotate (2 * m + 1) s)) = s(w t, w (finRotate (2 * m + 1) t))}
  have hbound := norm_sum_integral_prod_wignerMatrix_le (n := n) (r := m + 1)
    (by omega) hξp hηp hξ hη S fun w hw ↦ by
      have hv := card_image_le_div_two_add_one_of_no_singleton_nonloop_edge w (mem_filter.mp hw).2
      omega
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m + 1) = (n : ℝ) ^ m * Real.sqrt n := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [integral_trace_pow_wignerMatrix_of_ne hindep hξzero (by omega) hξp hηp,
    norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * (((m + 1 : ℕ) : ℝ) ^ (2 * m + 1) * (n : ℝ) ^ (m + 1) *
        (Real.sqrt n)⁻¹ ^ (2 * m + 1) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; push_cast; field_simp; ring

/-- **Quantitative even trace-moment bound.** For independent coordinates with centered
off-diagonal entries, unit off-diagonal second moments, and `2m`-th absolute moments bounded by
`B`, the normalized expected `2m`-th trace (`n ≠ 0`) is within `O(1 / n)` of `catalan m` for every
`m : ℕ`. Diagonal entries need not be centered. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le
    {m n : ℕ} (hn : n ≠ 0)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ)‖ ≤
      ((m : ℝ) ^ (2 * m) * B + catalan m * (m + 1).choose 2) / n := by
  have := hindep.isProbabilityMeasure
  rcases eq_or_ne m 0 with rfl | hm
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hB : 0 ≤ B := (by simp : (0 : ℝ) ≤ ∫ ω, ‖η 0 ω‖ ^ (2 * 0) ∂P).trans (hη 0)
    simp only [mul_zero, pow_zero, trace_one, Fintype.card_fin, integral_const, probReal_univ,
      one_smul, inv_mul_cancel₀ hnC, catalan_zero, Nat.cast_one, sub_self, norm_zero,
      Nat.cast_zero, one_mul, zero_add, Nat.choose_succ_self, mul_zero, add_zero]
    positivity
  · have hindep_ξ : iIndepFun ξ P := by
      simpa only [Function.comp_def, Sum.elim_inl] using hindep.precomp Sum.inl_injective
    have hrem := norm_inv_mul_integral_trace_pow_two_mul_sub_leading_le
      (n := n) hm hindep hξzero hξp hηp hξ hη
    rw [sum_integral_prod_wignerMatrix_leading (η := η) hm hindep_ξ hsecond, mul_sub] at hrem
    have hlead := norm_catalan_mul_descFactorial_inv_pow_sub_le (m := m) hn
    calc
      ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ)‖
        ≤ ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
            (n : ℂ)⁻¹ * ((catalan m * n.descFactorial (m + 1) : ℂ) * (n : ℂ)⁻¹ ^ m)‖ +
          ‖(n : ℂ)⁻¹ * ((catalan m * n.descFactorial (m + 1) : ℂ) * (n : ℂ)⁻¹ ^ m) -
            (catalan m : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (m : ℝ) ^ (2 * m) * B / n + (catalan m * (m + 1).choose 2 : ℝ) / n :=
          add_le_add hrem hlead
      _ = ((m : ℝ) ^ (2 * m) * B + catalan m * (m + 1).choose 2) / n := by ring

/-- The normalized expected `2m`-th trace of a Wigner matrix with independent coordinates and
centered unit-variance off-diagonal entries converges to `catalan m` for every `m : ℕ` (including
`m = 0`). Diagonal entries need not be centered. -/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix {m : ℕ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P)
      atTop (𝓝 (catalan m : ℂ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hlim : Tendsto
      (fun n : ℕ ↦ ((m : ℝ) ^ (2 * m) * B + catalan m * (m + 1).choose 2) / n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le
    hn hindep hξzero hsecond hξp hηp hξ hη

end TraceMoments

namespace Probability

section SpectralMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- On a finite measure space, the `k`-th empirical spectral moment of `wignerMatrix` is integrable
whenever all coordinates belong to `Lᵏ`. -/
theorem integrable_spectralMoment_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P) (n : ℕ) :
    Integrable (fun ω ↦ ∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) P := by
  simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin, RCLike.re_to_complex]
  exact ((integrable_trace_pow_wignerMatrix hξp hηp (n + 1)).re).const_mul _

/-- The expected `k`-th empirical spectral moment equals the real part of the normalized expected
`k`-th trace, without integrability hypotheses. -/
theorem integral_spectralMoment_wignerMatrix_eq_re (k n : ℕ) :
    (∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) =
      (((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ k).trace ∂P).re := by
  have htr : (∫ ω, (wignerMatrix ξ η (n + 1) ω ^ k).trace ∂P) =
      ((∫ ω, ((wignerMatrix ξ η (n + 1) ω ^ k).trace).re ∂P : ℝ) : ℂ) := by
    rw [integral_congr_ae (.of_forall fun ω ↦
      (ofReal_re_trace_pow_wignerMatrix (ξ := ξ) (η := η) (n + 1) k ω).symm)]
    exact integral_complex_ofReal
  simp_rw [Matrix.integral_pow_spectralMeasure, Fintype.card_fin, RCLike.re_to_complex,
    integral_const_mul, htr]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
    Nat.cast_add, Nat.cast_one]

/-- Quantitative `O(1 / (n + 1))` error bound for even expected empirical spectral moments (for all
`m, n : ℕ`). Diagonal entries need not be centered. -/
theorem abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_catalan_le (m n : ℕ)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    |(∫ ω, (∫ x, x ^ (2 * m) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) - catalan m| ≤
      ((m : ℝ) ^ (2 * m) * B + catalan m * (m + 1).choose 2) / (n + 1 : ℝ) := by
  rw [integral_spectralMoment_wignerMatrix_eq_re]
  have hc : (((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ (2 * m)).trace ∂P).re -
      (catalan m : ℝ) =
      (((n + 1 : ℕ) : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η (n + 1) ω ^ (2 * m)).trace ∂P) -
        (catalan m : ℂ)).re := by simp
  rw [hc]
  exact (Complex.abs_re_le_norm _).trans (by
    simpa [Nat.cast_add, Nat.cast_one] using
      norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le
        (Nat.succ_ne_zero n) hindep hξzero hsecond hξp hηp hξ hη)

/-- Quantitative `O(1 / √(n + 1))` error bound for odd expected empirical spectral moments. Neither
diagonal centering nor a second-moment assumption is required. -/
theorem abs_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le (m n : ℕ)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    {B : ℝ} (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m + 1 : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m + 1) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m + 1) ∂P ≤ B) :
    |∫ ω, (∫ x, x ^ (2 * m + 1) ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P| ≤
      (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℝ) := by
  rw [integral_spectralMoment_wignerMatrix_eq_re]
  exact (Complex.abs_re_le_norm _).trans (by
    simpa [Nat.cast_add, Nat.cast_one] using
      norm_inv_mul_integral_trace_pow_two_mul_add_one_of_ne_le
        m (n + 1) hindep hξzero hξp hηp hξ hη)

/-- **Expected spectral moment convergence for triangular Wigner arrays.** For jointly independent
coordinates at each size `n + 1` with centered unit-variance off-diagonal entries and uniformly
bounded `k`-th absolute moments, the expected `k`-th empirical spectral moment converges to the
`k`-th moment of the standard semicircle law `semicircleReal 0 1`. -/
theorem tendsto_integral_spectralMoment_wignerMatrix_array
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)}
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}
    {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) k (P n))
    (hηp : ∀ n i, MemLp (η n i) k (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [integral_pow_two_mul_semicircleReal_zero, NNReal.coe_one, one_pow, one_mul,
      ← tendsto_sub_nhds_zero_iff]
    have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim : Tendsto
        (fun n : ℕ ↦ ((m : ℝ) ^ (2 * m) * B + catalan m * (m + 1).choose 2) / (n + 1 : ℝ))
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul
        ((m : ℝ) ^ (2 * m) * B + catalan m * (m + 1).choose 2)
    exact squeeze_zero_norm (fun n ↦ by
      simpa only [Real.norm_eq_abs] using
        abs_integral_pow_two_mul_spectralMeasure_wignerMatrix_sub_catalan_le m n
          (hindep n) (hξzero n) (hsecond n) (hξp n) (hηp n) (hξ n) (hη n)) hlim
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero]
    have hlim : Tendsto (fun n : ℕ ↦ (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℝ))
        atTop (𝓝 0) := by
      have hsub : Tendsto (fun n : ℕ ↦ (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n)
          atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      exact (hsub.comp (tendsto_add_atTop_nat 1)).congr fun n ↦ by simp
    exact squeeze_zero_norm (fun n ↦ by
      simpa only [Real.norm_eq_abs] using
        abs_integral_pow_two_mul_add_one_spectralMeasure_wignerMatrix_le m n
          (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n)) hlim

/-- **Expected spectral moment convergence** to the standard semicircle moments for a fixed entry
array `(ξ, η)`. -/
theorem tendsto_integral_spectralMoment_wignerMatrix {k : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) idx) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ k ∂P ≤ B) (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ k ∂P ≤ B) :
    Tendsto (fun n ↦ ∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) :=
  tendsto_integral_spectralMoment_wignerMatrix_array
    (fun _ ↦ hindep) (fun _ ↦ hξzero) (fun _ ↦ hsecond)
    (fun _ ↦ hξp) (fun _ ↦ hηp) (fun _ ↦ hξ) (fun _ ↦ hη)

end SpectralMoments

end Probability

end TauCeti
