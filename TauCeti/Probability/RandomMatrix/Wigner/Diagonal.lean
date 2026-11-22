/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
import TauCeti.Analysis.Matrix.SpectralMeasure.ResolventStability
import TauCeti.Probability.Moments.Variance
import TauCeti.Probability.RandomMatrix.Diagonal

/-!
# Diagonal perturbations of Wigner matrices

Setting the diagonal to zero changes the empirical spectral transform by at most
the normalized Euclidean size of the diagonal times the inverse squared imaginary
part of the parameter. The mean bound uses the normalized sum of diagonal second
moments and applies to triangular arrays.

An identically distributed, pairwise independent real diagonal does not change the almost-sure
weak spectral limits, without any diagonal moment assumption. This separates the arbitrary
diagonal law from the finite-second-moment off-diagonal hypotheses in the semicircle law.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), proof of Theorem 2.1.
-/

public section

open MeasureTheory Matrix Finset

namespace TauCeti.Probability

variable {Ω : Type*}
variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}

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
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
  refine mul_le_mul_of_nonneg_left
    ((le_of_abs_le (abs_integral_le_sqrt_integral_sq he)).trans_eq ?_) (sq_nonneg _)
  simp_rw [Real.sq_sqrt (hS _)]
  unfold S
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hi i)]

section AlmostSure

open Filter ProbabilityTheory
open scoped Topology

variable [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

variable (ξ η) in
/-- A Wigner family with an identically distributed, pairwise independent real diagonal has
the same weak spectral limits as its zero-diagonal version, almost surely, without any
diagonal moment assumption. The upper entries may be arbitrary and may depend on the diagonal. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_iff
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

end AlmostSure

end TauCeti.Probability
