/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Diagonal
public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Probability.StrongLaw
import TauCeti.Probability.Moments.Variance

/-!
# Removing the diagonal of a random matrix

Adding a real i.i.d. diagonal divided by a normalization tending to infinity preserves almost
sure weak spectral limits of Hermitian matrix families. Pairwise independence of the diagonal
coordinates suffices. No diagonal moment, centering, or independence from the matrix family is
required. The full-measure event works for every limiting probability measure at once.

In particular a Wigner matrix and its zero-diagonal version have the same almost-sure weak
spectral limits. This separates the arbitrary diagonal law from the finite-second-moment
off-diagonal hypotheses in the semicircle law. The result concerns global spectral limits;
individual extreme eigenvalues need not be stable under these perturbations.

The pointwise and mean absolute resolvent bounds also apply to triangular arrays with
non-identically distributed diagonal entries. They control the transform error through the
normalized Euclidean size of the diagonal and its mean square, respectively.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), proof of Theorem 2.1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix Finset
open scoped Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Adding an identically distributed, pairwise independent real diagonal divided by any
normalization tending to infinity preserves weak spectral limits almost surely. There is no
moment assumption on the diagonal and no independence assumption involving the matrices. -/
theorem ae_tendsto_spectralMeasure_add_diagonal_div_iff {𝕜 : Type*} [RCLike 𝕜]
    (A : (n : ℕ) → Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (hA : ∀ n ω, (A n ω).IsHermitian) (η : ℕ → Ω → ℝ)
    (hindep : Pairwise fun i j ↦ IndepFun (η i) (η j) P)
    (hid : ∀ i, IdentDistrib (η i) (η 0) P P)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) :
    ∀ᵐ ω ∂P, ∀ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n ↦
        (A n ω + diagonal (fun i : Fin (n + 1) ↦ ((η i ω / b (n + 1) : ℝ) : 𝕜))).spectralMeasure
          ((hA n ω).add (isHermitian_diagonal_ofReal _)))
        atTop (𝓝 μ) ↔
      Tendsto (fun n ↦ (A n ω).spectralMeasure (hA n ω)) atTop (𝓝 μ) := by
  classical
  filter_upwards [ae_tendsto_card_filter_norm_gt_div η hindep hid] with ω hω
  intro μ
  apply Matrix.tendsto_spectralMeasure_add_diagonal_iff
  intro ε hε
  have hlarge := hω (fun n ↦ ε * b n) (hb.const_mul_atTop hε)
  have hshift := hlarge.comp (tendsto_add_atTop_nat 1)
  apply hshift.congr'
  filter_upwards [((hb.comp (tendsto_add_atTop_nat 1)).eventually
    (eventually_gt_atTop 0))] with n hn
  simp only [Function.comp_apply] at hn
  simp only [Function.comp_apply, Fintype.card_fin, Real.norm_eq_abs]
  congr 1
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.1 hi, abs_div, abs_of_pos hn, lt_div_iff₀ hn]

/-- A Wigner family with an identically distributed, pairwise independent real diagonal has
the same weak spectral limits as its zero-diagonal version, almost surely, without any
diagonal moment assumption. The upper entries may be arbitrary and may depend on the diagonal. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_iff
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (hindep : Pairwise fun i j ↦ IndepFun (η i) (η j) P)
    (hid : ∀ i, IdentDistrib (η i) (η 0) P P) :
    ∀ᵐ ω ∂P, ∀ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n ↦ (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))) atTop (𝓝 μ) ↔
      Tendsto (fun n ↦ (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1))) atTop (𝓝 μ) := by
  have h := ae_tendsto_spectralMeasure_add_diagonal_div_iff
    (fun n ω ↦ wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω)
    (fun n ω ↦ wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))
    η hindep hid (fun n ↦ Real.sqrt n)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [h] with ω hω
  simpa only [wignerMatrix_eq_add_diagonal ξ η, RCLike.ofReal_eq_complex_ofReal] using
    fun μ ↦ (hω μ).symm

section MeanSquare

variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}

omit [MeasurableSpace Ω] in
open scoped Matrix.Norms.Frobenius in
/-- The transform error from setting the diagonal to zero is bounded by the normalized
Euclidean norm of the diagonal times `(Im z)⁻²`. -/
theorem norm_resolventTransform_wignerMatrix_sub_wignerMatrix_zero_le (ω : Ω)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
      resolventTransform ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z‖ ≤
      z.im⁻¹ ^ 2 * Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 * ∑ i : Fin (n + 1), η i ω ^ 2) := by
  let B := diagonal (fun i : Fin (n + 1) ↦ ((η i ω / Real.sqrt (n + 1) : ℝ) : ℂ))
  have hB : wignerMatrix ξ η (n + 1) ω - wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω = B := by
    simp only [B, wignerMatrix_eq_add_diagonal ξ η, add_sub_cancel_left, Nat.cast_succ]
  have hs : ‖B‖ ^ 2 = (n + 1 : ℝ)⁻¹ * ∑ i : Fin (n + 1), η i ω ^ 2 := by
    dsimp only [B]
    rw [frobenius_norm_diagonal, PiLp.norm_sq_eq_of_L2, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      Real.sq_sqrt (by positivity), div_eq_inv_mul]
  have hnorm : ‖B‖ / Real.sqrt (n + 1 : ℝ) =
      Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 * ∑ i : Fin (n + 1), η i ω ^ 2) := by
    rw [← Real.sqrt_sq (div_nonneg (norm_nonneg B) (Real.sqrt_nonneg _)), div_pow, hs,
      Real.sq_sqrt (by positivity)]
    congr 1
    ring
  have hp := norm_resolventTransform_spectralMeasure_sub_le_frobenius
    (wignerMatrix_isHermitian ξ η ω (n + 1))
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) hz
  simpa only [hB, Fintype.card_fin, Nat.cast_succ, ← inv_pow, sq_abs, inv_pow,
    mul_div_assoc, hnorm] using hp

/-- The mean transform error from setting the diagonal to zero is bounded using only
the normalized sum of diagonal second moments. -/
theorem integral_norm_resolventTransform_wignerMatrix_sub_wignerMatrix_zero_le
    [IsProbabilityMeasure P]
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, MemLp (η i) 2 P) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ ω, ‖resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
      resolventTransform ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z‖ ∂P) ≤
      z.im⁻¹ ^ 2 * Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 *
        ∑ i : Fin (n + 1), ∫ ω, η i ω ^ 2 ∂P) := by
  let S (ω : Ω) := (n + 1 : ℝ)⁻¹ ^ 2 * ∑ i : Fin (n + 1), η i ω ^ 2
  have hS (ω : Ω) : 0 ≤ S ω := by unfold S; positivity
  have hi (i : Fin (n + 1)) : Integrable (fun ω ↦ η i ω ^ 2) P := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (hη i i.isLt).aestronglyMeasurable).mp (hη i i.isLt)
  have hSi : Integrable S P := (integrable_finsetSum _ fun i _ ↦ hi i).const_mul _
  have he : MemLp (fun ω ↦ Real.sqrt (S ω)) 2 P := by
    refine (memLp_two_iff_integrable_sq_norm
      (Real.continuous_sqrt.comp_aestronglyMeasurable hSi.aestronglyMeasurable)).mpr ?_
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hS _)] using hSi
  have ha := (aemeasurable_wignerMatrix hξ (fun i hi ↦ (hη i hi).aemeasurable))
    |>.integrable_resolventTransform_spectralMeasure
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hz
  have hb := (aemeasurable_wignerMatrix hξ (fun _ _ ↦ aemeasurable_const))
    |>.integrable_resolventTransform_spectralMeasure
    (fun ω ↦ wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) hz
  have hab := (ha.sub hb).norm
  refine (integral_mono hab ((he.integrable one_le_two).const_mul _)
    (fun ω ↦ norm_resolventTransform_wignerMatrix_sub_wignerMatrix_zero_le
      (ξ := ξ) (η := η) ω hz)).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ((integral_le_sqrt_integral_sq he).trans_eq ?_) (sq_nonneg _)
  simp_rw [Real.sq_sqrt (hS _)]
  unfold S
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hi i)]

end MeanSquare

end TauCeti.Probability
