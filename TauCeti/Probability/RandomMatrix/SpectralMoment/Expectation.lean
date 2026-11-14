/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.RandomMatrix.MomentBounds
import TauCeti.Probability.UniformSampling

/-!
# Expected moments of Wigner matrices and Catalan limits

In the trace-word expansion of a normalized Wigner matrix `Hₙ = wignerMatrix ξ η n`, words with a
singleton nonloop unordered edge have expectation zero as soon as the strictly upper entries have
mean zero, while nonleading words visit at most `m` vertices and contribute `O_m(n⁻¹)` to
`n⁻¹ E[tr(Hₙ^(2m))]`. Each of the `n.descFactorial (m + 1) * catalan m` leading words of length
`2m` canonicalizes to a closed tree walk without loops and contributes `n⁻ᵐ` when the strictly
upper entries have unit second absolute moment.

Combining the leading tree-word evaluation with the collision bound for `n.descFactorial (m + 1)`
yields an explicit `O_m(n⁻¹)` bound for `‖n⁻¹ E[tr(Hₙ^(2m))] - catalan m‖` and `O_m(n^(-1/2))` for
expected odd normalized traces, without requiring diagonal centering or identical entry laws.
Passing to `n → ∞` identifies the limiting expected moments of the empirical spectral measure with
the moments of `semicircleReal 0 1`, including for triangular arrays on varying probability spaces.

## Main results

* `TauCeti.sum_integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one`: the leading
  even trace-word sum equals `n.descFactorial (m + 1) * catalan m * n⁻ᵐ`.
* `TauCeti.norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le`: nonasymptotic
  `O_m(n⁻¹)` error bound comparing `n⁻¹ E[tr(Hₙ^(2m))]` to `catalan m`.
* `TauCeti.norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le_of_upper_zero`:
  nonasymptotic `O_m(n^(-1/2))` bound for expected normalized odd traces under off-diagonal
  centering.
* `TauCeti.tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix` and
  `TauCeti.tendsto_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_of_upper_zero`:
  asymptotic trace-moment limits for triangular Wigner arrays.
* `TauCeti.tendsto_integral_pow_spectralMeasure_wignerMatrix`: expected `k`th empirical spectral
  moments converge to `∫ x^k d(semicircleReal 0 1)` for every `k : ℕ`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open TauCeti.TreeWalk TauCeti.Probability
open scoped Topology ENNReal

namespace TauCeti

section FixedSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Every power of a Wigner matrix has integrable trace on a finite measure space when the array
entries have finite `k`th moments. -/
theorem integrable_trace_pow_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P) (n : ℕ) :
    Integrable (fun ω ↦ (wignerMatrix ξ η n ω ^ k).trace) P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp_rw [trace_pow_eq_sum_prod _ hk]
    exact integrable_finsetSum _ fun w _ ↦
      integrable_prod_wignerMatrix_apply (by simpa using hξp) (by simpa using hηp) _ _

/-- The expected `k`th empirical spectral moment of `wignerMatrix ξ η (n + 1)` is the real part of
its normalized expected trace. -/
theorem integral_integral_pow_spectralMeasure_wignerMatrix [IsFiniteMeasure P] {k : ℕ}
    (hξp : ∀ ij, MemLp (ξ ij) k P) (hηp : ∀ i, MemLp (η i) k P) (n : ℕ) :
    (∫ ω, (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P) =
      (((n + 1 : ℕ) : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η (n + 1) ω ^ k).trace ∂P).re := by
  have hpoint (ω : Ω) :
      (∫ x, x ^ k ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      (((n + 1 : ℕ) : ℂ)⁻¹ * (wignerMatrix ξ η (n + 1) ω ^ k).trace).re := by
    rw [Matrix.integral_pow_spectralMeasure]
    simp only [Fintype.card_fin, RCLike.re_to_complex, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  simp_rw [hpoint]
  have hint := (integrable_trace_pow_wignerMatrix hξp hηp (n + 1)).const_mul
    (((n + 1 : ℕ) : ℂ)⁻¹)
  simpa only [Complex.reCLM_apply, integral_const_mul] using
    Complex.reCLM.integral_comp_comm hint

/-- Summing over all leading cyclic trace words of positive length `2 * m` gives
`n.descFactorial (m + 1) * catalan m * n⁻ᵐ` whenever the strictly upper entries are independent
with unit second absolute moment. -/
theorem sum_integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one
    {m n : ℕ} [NeZero m] (hindep : iIndepFun ξ P)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1) :
    ∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P =
      (n.descFactorial (m + 1) : ℂ) * catalan m * (n : ℂ)⁻¹ ^ m := by
  have hterm (w : Fin (2 * m) → Fin n)
      (hw : w ∈ ({w : Fin (2 * m) → Fin n |
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1} : Finset _)) :
      ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P = (n : ℂ)⁻¹ ^ m := by
    obtain ⟨h, hv⟩ := (mem_filter.mp hw).2
    exact integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one hindep hsecond w h hv
  rw [sum_congr rfl hterm, sum_const, card_filter_no_singleton_edge_and_card_image_eq]
  simp [Fintype.card_fin, mul_assoc]

/-- Under off-diagonal centering alone, subtracting the leading tree-word sum from the expected
even trace and normalizing by `n⁻¹` leaves a remainder of norm at most `m^(2m) B / n` (`m ≠ 0`). -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le_of_upper_zero
    {m n : ℕ} (hm : m ≠ 0) {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
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
  have hlead : ({w ∈ S | #(univ.image w) = m + 1} : Finset (Fin (2 * m) → Fin n)) =
      ({w : Fin (2 * m) → Fin n |
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1} : Finset (Fin (2 * m) → Fin n)) := by
    ext w
    simp only [S, mem_filter, mem_univ, true_and]
    refine ⟨fun ⟨h, hv⟩ ↦ ⟨fun t ↦ h t
      ((ne_and_card_edge_fiber_eq_two_of_no_singleton_nonloop_edge_of_card_image_eq w h hv).1 t),
      hv⟩, fun ⟨h, hv⟩ ↦ ⟨fun t _ ↦ h t, hv⟩⟩
  have hsplit : (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      ∑ w ∈ S with #(univ.image w) = m + 1, F w =
        ∑ w ∈ S with #(univ.image w) ≠ m + 1, F w := by
    rw [integral_trace_pow_wignerMatrix_of_upper_zero hindep hξzero (by omega) hξp hηp]
    exact sub_eq_iff_eq_add.mpr (by
      simpa only [S, F, add_comm] using
        (sum_filter_add_sum_filter_not S (fun w ↦ #(univ.image w) = m + 1) F).symm)
  have hbound := norm_sum_integral_prod_wignerMatrix_le (n := n) (r := m)
    (by omega) hξp hηp hξ hη (S.filter fun w ↦ #(univ.image w) ≠ m + 1) fun w hw ↦ by
      obtain ⟨hwS, hwne⟩ := mem_filter.mp hw
      have hv := card_image_le_div_two_add_one_of_no_singleton_nonloop_edge w (mem_filter.mp hwS).2
      omega
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m) = (n : ℝ) ^ m := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← hlead]
  rw [hsplit, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((m : ℝ) ^ (2 * m) * (n : ℝ) ^ m * (Real.sqrt n)⁻¹ ^ (2 * m) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; field_simp

private theorem one_sub_descFactorial_div_pow_le {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    0 ≤ 1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) ∧
      1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) ≤ ((m + 1).choose 2 : ℝ) / n := by
  let _ : MeasurableSpace (Fin n) := ⊤
  have : MeasurableSingletonClass (Fin n) := ⟨fun _ ↦ trivial⟩
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have hle_pow : (n.descFactorial (m + 1) : ℝ) ≤ (n : ℝ) ^ (m + 1) := by
    exact_mod_cast Nat.descFactorial_le_pow n (m + 1)
  have hdiv_le : (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr hle_pow
  refine ⟨sub_nonneg.mpr hdiv_le, ?_⟩
  have henn : (1 : ℝ≥0∞) - (n.descFactorial (m + 1) : ℝ≥0∞) / (n : ℝ≥0∞) ^ (m + 1) ≤
      ((m + 1).choose 2 : ℝ≥0∞) / n := by
    have heq := uniformOn_not_injective_apply_eq (ι := Fin (m + 1)) (κ := Fin n)
    have hub := uniformOn_not_injective_le (ι := Fin (m + 1)) (κ := Fin n)
    simpa only [Fintype.card_fin] using heq.symm.trans_le hub
  have hne_top : ((m + 1).choose 2 : ℝ≥0∞) / n ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [hn])
  have htoReal := ENNReal.toReal_mono hne_top henn
  have hdiv_enn_le : (n.descFactorial (m + 1) : ℝ≥0∞) / (n : ℝ≥0∞) ^ (m + 1) ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (pow_ne_zero _ (by simp [hn]))) (Or.inl (by simp))]
    simpa only [one_mul] using (by exact_mod_cast Nat.descFactorial_le_pow n (m + 1) :
      (n.descFactorial (m + 1) : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ (m + 1))
  rw [ENNReal.toReal_sub_of_le hdiv_enn_le ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast] at htoReal
  exact htoReal

/-- **Quantitative Catalan bound for expected even Wigner moments.** When `n ≠ 0`, the array
coordinates are independent, the strictly upper entries have mean zero and unit second absolute
moment, and all `2m`th absolute moments are bounded by `B`, the normalized expected `2m`th trace
differs from `catalan m` by at most `((m + 1).choose 2 * catalan m + m^(2m) * B) / n`. No diagonal
centering or identical-distribution hypothesis is needed, and `m = 0` is included. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le
    {m n : ℕ} (hn : n ≠ 0) {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hsecond : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B) :
    ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ)‖ ≤
      (((m + 1).choose 2 * catalan m : ℕ) + (m : ℝ) ^ (2 * m) * B) / n := by
  have := hindep.isProbabilityMeasure
  rcases eq_or_ne m 0 with rfl | hm
  · have h1B : 1 ≤ B := by simpa using hη 0
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simpa [hnC] using div_nonneg (by linarith) (Nat.cast_nonneg n)
  · have : NeZero m := ⟨hm⟩
    have hindepξ : iIndepFun ξ P := by simpa using hindep.precomp Sum.inl_injective
    let L : ℂ := ∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P
    have hrem : ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (n : ℂ)⁻¹ * L‖ ≤
        (m : ℝ) ^ (2 * m) * B / n := by
      rw [← mul_sub]
      exact norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le_of_upper_zero
        hm hindep hξzero hξp hηp hξ hη
    have hL : (n : ℂ)⁻¹ * L - (catalan m : ℂ) =
        ((((n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) - 1) * catalan m : ℝ) : ℂ) := by
      dsimp only [L]
      rw [sum_integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq_one hindepξ hsecond]
      push_cast
      rw [div_eq_mul_inv, inv_pow]
      ring
    obtain ⟨hnonneg, hcoll⟩ := one_sub_descFactorial_div_pow_le hn m
    have hL_norm : ‖(n : ℂ)⁻¹ * L - (catalan m : ℂ)‖ ≤
        ((m + 1).choose 2 * catalan m : ℕ) / n := by
      rw [hL, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonpos (by linarith : (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1) - 1 ≤ 0),
        neg_sub, abs_of_nonneg (Nat.cast_nonneg (catalan m))]
      calc
        (1 - (n.descFactorial (m + 1) : ℝ) / (n : ℝ) ^ (m + 1)) * (catalan m : ℝ) ≤
            (((m + 1).choose 2 : ℝ) / n) * (catalan m : ℝ) :=
          mul_le_mul_of_nonneg_right hcoll (Nat.cast_nonneg _)
        _ = ((m + 1).choose 2 * catalan m : ℕ) / n := by push_cast; ring
    calc
      ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (catalan m : ℂ)‖ ≤
          ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - (n : ℂ)⁻¹ * L‖ +
            ‖(n : ℂ)⁻¹ * L - (catalan m : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ ((n : ℂ)⁻¹ * L) _
      _ ≤ (m : ℝ) ^ (2 * m) * B / n + ((m + 1).choose 2 * catalan m : ℕ) / n :=
        add_le_add hrem hL_norm
      _ = (((m + 1).choose 2 * catalan m : ℕ) + (m : ℝ) ^ (2 * m) * B) / n := by ring

/-- Under off-diagonal centering alone, the expected normalized odd Wigner moment has norm at most
`(m + 1)^(2m + 1) B / √n`. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le_of_upper_zero
    {m n : ℕ} {B : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m + 1 : ℕ) P)
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
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : (Real.sqrt n) ^ (2 * m + 1) = (n : ℝ) ^ m * Real.sqrt n := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [integral_trace_pow_wignerMatrix_of_upper_zero hindep hξzero (by omega) hξp hηp,
    norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)⁻¹ * (((m + 1 : ℕ) : ℝ) ^ (2 * m + 1) * (n : ℝ) ^ (m + 1) *
        (Real.sqrt n)⁻¹ ^ (2 * m + 1) * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [inv_pow, hs]; push_cast; field_simp; ring

end FixedSpace

section TriangularArray

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
  {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ} {η : (n : ℕ) → ℕ → Ω n → ℝ}

/-- Expected normalized `2m`th traces of a triangular Wigner array converge to `catalan m` for
every `m : ℕ` when the entries are row-wise independent, the upper entries are centered with unit
second absolute moment, and the `2m`th absolute moments are uniformly bounded. -/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix {m : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) k) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * m : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * m : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * m) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * m) ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦
      (n : ℂ)⁻¹ * ∫ ω, (wignerMatrix (ξ n) (η n) n ω ^ (2 * m)).trace ∂P n)
      atTop (𝓝 (catalan m : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ ↦
      (((m + 1).choose 2 * catalan m : ℕ) + (m : ℝ) ^ (2 * m) * B) / n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le hn
    (hindep n) (hξzero n) (hsecond n) (hξp n) (hηp n) (hξ n) (hη n)

/-- Expected normalized odd traces of a triangular Wigner array converge to zero under row-wise
independence, off-diagonal centering, and uniformly bounded `(2m + 1)`st absolute moments. -/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_of_upper_zero
    {m : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) k) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hξp : ∀ n ij, MemLp (ξ n ij) (2 * m + 1 : ℕ) (P n))
    (hηp : ∀ n i, MemLp (η n i) (2 * m + 1 : ℕ) (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ (2 * m + 1) ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ (2 * m + 1) ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦
      (n : ℂ)⁻¹ * ∫ ω, (wignerMatrix (ξ n) (η n) n ω ^ (2 * m + 1)).trace ∂P n)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  exact squeeze_zero_norm (fun n ↦
    norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le_of_upper_zero
      (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n)) hlim

/-- **Expected spectral moments converge to semicircle moments.** For every `k : ℕ`, the expected
`k`th moment of the empirical spectral measure of `wignerMatrix (ξ n) (η n) (n + 1)` converges to
`∫ x^k d(semicircleReal 0 1)` under row-wise independence, off-diagonal centering, unit
off-diagonal second absolute moments, and uniformly bounded `k`th absolute moments. -/
theorem tendsto_integral_pow_spectralMeasure_wignerMatrix {k : ℕ} {B : ℝ}
    (hindep : ∀ n, iIndepFun (fun idx : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) idx) (P n))
    (hξzero : ∀ n ij, ∫ ω, ξ n ij ω ∂P n = 0)
    (hsecond : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hξp : ∀ n ij, MemLp (ξ n ij) k (P n))
    (hηp : ∀ n i, MemLp (η n i) k (P n))
    (hξ : ∀ n ij, ∫ ω, ‖ξ n ij ω‖ ^ k ∂P n ≤ B)
    (hη : ∀ n i, ∫ ω, ‖η n i ω‖ ^ k ∂P n ≤ B) :
    Tendsto (fun n : ℕ ↦
      ∫ ω, (∫ x, x ^ k ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal 0 1)) := by
  have _ (n : ℕ) := (hindep n).isProbabilityMeasure
  simp_rw [fun n ↦ integral_integral_pow_spectralMeasure_wignerMatrix (hξp n) (hηp n) n]
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [integral_pow_two_mul_semicircleReal_zero, NNReal.coe_one, one_pow, one_mul]
    have hcomplex : Tendsto (fun n : ℕ ↦
        ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∫ ω, (wignerMatrix (ξ n) (η n) (n + 1) ω ^ (2 * m)).trace ∂P n)
        atTop (𝓝 (catalan m : ℂ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n : ℕ ↦
          (((m + 1).choose 2 * catalan m : ℕ) + (m : ℝ) ^ (2 * m) * B) / (n + 1 : ℕ))
          atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun n ↦ norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_catalan_le
          (Nat.succ_ne_zero n) (hindep n) (hξzero n) (hsecond n) (hξp n) (hηp n) (hξ n) (hη n))
        hlim
    simpa only [Function.comp_def, Complex.natCast_re] using
      (Complex.continuous_re.tendsto (catalan m : ℂ)).comp hcomplex
  · rw [integral_pow_two_mul_add_one_semicircleReal_zero]
    have hcomplex : Tendsto (fun n : ℕ ↦
        ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∫ ω, (wignerMatrix (ξ n) (η n) (n + 1) ω ^ (2 * m + 1)).trace ∂P n)
        atTop (𝓝 0) := by
      have hlim : Tendsto (fun n : ℕ ↦
          (m + 1 : ℝ) ^ (2 * m + 1) * B / Real.sqrt (n + 1 : ℕ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop
          (Real.tendsto_sqrt_atTop.comp
            (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
      exact squeeze_zero_norm
        (fun n ↦ norm_inv_mul_integral_trace_pow_two_mul_add_one_wignerMatrix_le_of_upper_zero
          (hindep n) (hξzero n) (hξp n) (hηp n) (hξ n) (hη n)) hlim
    simpa only [Function.comp_def, Complex.zero_re] using
      (Complex.continuous_re.tendsto (0 : ℂ)).comp hcomplex

end TriangularArray

end TauCeti
