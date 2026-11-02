/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Covariance and pseudocovariance of proper complex Gaussians

For Hermitian positive semidefinite `C`, the complex covariance of
`properComplexGaussianMeasure m C` is `C`, and its complex pseudocovariance is zero.
Both statements use centered coordinate products and include
their integrability. Thus the factor one half and the signs of the off-diagonal blocks
in the real covariance agree with the proper complex convention, including singular laws.
The squared modulus of each centered coordinate is integrable and has mean its complex variance.

The proofs use Mathlib's real Gaussian coordinate covariance and Fernique integrability.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every complex coordinate has all finite absolute moments, including at invalid
covariances where the law is a point mass. -/
theorem memLp_apply_properComplexGaussianMeasure (m : ι → ℂ) (C : Matrix ι ι ℂ)
    (i : ι) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun z ↦ z i) p (properComplexGaussianMeasure m C) :=
  (IsGaussian.memLp_id _ p hp).continuousLinearMap_comp
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ)

/-- Centered products defining the complex covariance are integrable at all parameters. -/
theorem integrable_mul_conj_sub_properComplexGaussianMeasure (m : ι → ℂ)
    (C : Matrix ι ι ℂ) (i j : ι) :
    Integrable (fun z ↦ (z i - m i) * star (z j - m j))
      (properComplexGaussianMeasure m C) := by
  have h k := (memLp_apply_properComplexGaussianMeasure m C k 2 (by simp)).sub
    (memLp_const (m k))
  exact (h i).integrable_mul (h j).star

/-- Centered products defining the complex pseudocovariance are integrable at all
parameters. -/
theorem integrable_mul_sub_properComplexGaussianMeasure (m : ι → ℂ)
    (C : Matrix ι ι ℂ) (i j : ι) :
    Integrable (fun z ↦ (z i - m i) * (z j - m j)) (properComplexGaussianMeasure m C) := by
  have h k := (memLp_apply_properComplexGaussianMeasure m C k 2 (by simp)).sub
    (memLp_const (m k))
  exact (h i).integrable_mul (h j)

private theorem integrable_real_centered_product (m : ι → ℂ) (C : Matrix ι ι ℂ)
    (a b : ι ⊕ ι) :
    Integrable (fun z ↦
      (complexToRealEuclidean ι z a - complexToRealEuclidean ι m a) *
      (complexToRealEuclidean ι z b - complexToRealEuclidean ι m b))
      (properComplexGaussianMeasure m C) := by
  have h k := (IsGaussian.memLp_dual (properComplexGaussianMeasure m C)
    ((EuclideanSpace.proj k).comp (complexToRealEuclidean ι).toContinuousLinearMap)
    2 (by simp)).sub (memLp_const (complexToRealEuclidean ι m k))
  exact (h a).integrable_mul (h b)

private theorem integral_real_centered_product (m : ι → ℂ) {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) (a b : ι ⊕ ι) :
    ∫ z, (complexToRealEuclidean ι z a - complexToRealEuclidean ι m a) *
        (complexToRealEuclidean ι z b - complexToRealEuclidean ι m b)
        ∂properComplexGaussianMeasure m C = complexGaussianRealCovariance C a b := by
  have h := covarianceBilinDual_eq_covariance
    (μ := multivariateGaussian (complexToRealEuclidean ι m) (complexGaussianRealCovariance C))
    IsGaussian.memLp_two_id (EuclideanSpace.proj a) (EuclideanSpace.proj b)
  rw [covarianceBilinDual_apply' IsGaussian.memLp_two_id,
    integral_id_multivariateGaussian'] at h
  simp only [map_sub, EuclideanSpace.coe_proj] at h
  rw [covariance_eval_multivariateGaussian
    ((posSemidef_complexGaussianRealCovariance_iff C).2 hC)] at h
  rw [← map_complexToRealEuclidean_properComplexGaussianMeasure m C,
    integral_map (by fun_prop) (by fun_prop)] at h
  exact h

private theorem integrable_re_im_centered_products (m : ι → ℂ) (C : Matrix ι ι ℂ)
    (i j : ι) :
    Integrable (fun z ↦ ((z i).re - (m i).re) * ((z j).re - (m j).re))
        (properComplexGaussianMeasure m C) ∧
    Integrable (fun z ↦ ((z i).im - (m i).im) * ((z j).im - (m j).im))
        (properComplexGaussianMeasure m C) ∧
    Integrable (fun z ↦ ((z i).re - (m i).re) * ((z j).im - (m j).im))
        (properComplexGaussianMeasure m C) ∧
    Integrable (fun z ↦ ((z i).im - (m i).im) * ((z j).re - (m j).re))
        (properComplexGaussianMeasure m C) := by
  have h := integrable_real_centered_product m C
  simpa only [complexToRealEuclidean_apply, Sum.elim_inl, Sum.elim_inr] using
    And.intro (h (Sum.inl i) (Sum.inl j))
      (And.intro (h (Sum.inr i) (Sum.inr j))
        (And.intro (h (Sum.inl i) (Sum.inr j)) (h (Sum.inr i) (Sum.inl j))))

private theorem integral_re_im_centered_products (m : ι → ℂ) {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) (i j : ι) :
    (∫ z, ((z i).re - (m i).re) * ((z j).re - (m j).re)
        ∂properComplexGaussianMeasure m C) = (C i j).re / 2 ∧
    (∫ z, ((z i).im - (m i).im) * ((z j).im - (m j).im)
        ∂properComplexGaussianMeasure m C) = (C i j).re / 2 ∧
    (∫ z, ((z i).re - (m i).re) * ((z j).im - (m j).im)
        ∂properComplexGaussianMeasure m C) = -(C i j).im / 2 ∧
    (∫ z, ((z i).im - (m i).im) * ((z j).re - (m j).re)
        ∂properComplexGaussianMeasure m C) = (C i j).im / 2 := by
  have h := integral_real_centered_product m hC
  simpa only [complexToRealEuclidean_apply, Sum.elim_inl, Sum.elim_inr,
    complexGaussianRealCovariance_inl_inl, complexGaussianRealCovariance_inr_inr,
    complexGaussianRealCovariance_inl_inr, complexGaussianRealCovariance_inr_inl] using
    And.intro (h (Sum.inl i) (Sum.inl j))
      (And.intro (h (Sum.inr i) (Sum.inr j))
        (And.intro (h (Sum.inl i) (Sum.inr j)) (h (Sum.inr i) (Sum.inl j))))

/-- The complex covariance of a proper complex Gaussian is its covariance parameter. -/
theorem integral_mul_conj_sub_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i j : ι) :
    ∫ z, (z i - m i) * star (z j - m j) ∂properComplexGaussianMeasure m C = C i j := by
  have hint := integrable_mul_conj_sub_properComplexGaussianMeasure m C i j
  obtain ⟨hrr_int, hii_int, hri_int, hir_int⟩ := integrable_re_im_centered_products m C i j
  obtain ⟨hrr, hii, hri, hir⟩ := integral_re_im_centered_products m hC i j
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hint, RCLike.re_eq_complex_re]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
    rw [integral_add hrr_int hii_int, hrr, hii]
    ring
  · rw [← RCLike.im_eq_complex_im, ← integral_im hint, RCLike.im_eq_complex_im]
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, mul_neg]
    rw [integral_add]
    · rw [integral_neg, hri, hir]
      ring
    · simpa only [Pi.neg_def] using hri_int.neg
    · exact hir_int

/-- The complex pseudocovariance of a proper complex Gaussian vanishes. -/
theorem integral_mul_sub_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i j : ι) :
    ∫ z, (z i - m i) * (z j - m j) ∂properComplexGaussianMeasure m C = 0 := by
  have hint := integrable_mul_sub_properComplexGaussianMeasure m C i j
  obtain ⟨hrr_int, hii_int, hri_int, hir_int⟩ := integrable_re_im_centered_products m C i j
  obtain ⟨hrr, hii, hri, hir⟩ := integral_re_im_centered_products m hC i j
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hint, RCLike.re_eq_complex_re]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.zero_re]
    rw [integral_sub hrr_int hii_int, hrr, hii]
    ring
  · rw [← RCLike.im_eq_complex_im, ← integral_im hint, RCLike.im_eq_complex_im]
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.zero_im]
    rw [integral_add hri_int hir_int, hri, hir]
    ring

/-- The squared modulus of a centered complex Gaussian coordinate is integrable, including
zero and invalid covariance parameters. -/
theorem integrable_norm_sq_sub_eval_properComplexGaussianMeasure (m : ι → ℂ)
    (C : Matrix ι ι ℂ) (i : ι) :
    Integrable (fun z ↦ ‖z i - m i‖ ^ 2) (properComplexGaussianMeasure m C) := by
  simpa only [RCLike.re_eq_complex_re, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq] using
    (integrable_mul_conj_sub_properComplexGaussianMeasure m C i i).re

/-- The mean squared modulus of a centered proper complex Gaussian coordinate is its
complex variance. In particular, it is one for a standard coordinate. -/
@[simp]
theorem integral_norm_sq_sub_eval_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i : ι) :
    ∫ z, ‖z i - m i‖ ^ 2 ∂properComplexGaussianMeasure m C = (C i i).re := by
  simpa only [RCLike.re_eq_complex_re, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq] using
    (integral_re (integrable_mul_conj_sub_properComplexGaussianMeasure m C i i)).trans
      (congrArg RCLike.re (integral_mul_conj_sub_properComplexGaussianMeasure m hC i i))

end TauCeti.Probability
