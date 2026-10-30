/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.ProperComplexGaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Covariance and pseudocovariance of proper complex Gaussians

For Hermitian positive semidefinite `C`, the complex covariance of
`properComplexGaussianMeasure m C` is `C`, and its complex pseudocovariance is zero.
Both statements use centered coordinate products and include
their integrability. Thus the factor one half and the signs of the off-diagonal blocks
in the real covariance agree with the proper complex convention, including singular laws.

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
      (Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im) a -
        Sum.elim (fun i ↦ (m i).re) (fun i ↦ (m i).im) a) *
      (Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im) b -
        Sum.elim (fun i ↦ (m i).re) (fun i ↦ (m i).im) b))
      (properComplexGaussianMeasure m C) := by
  have h k := (IsGaussian.memLp_dual (properComplexGaussianMeasure m C)
    ((EuclideanSpace.proj k).comp (complexToRealEuclidean ι).toContinuousLinearMap)
    2 (by simp)).sub (memLp_const (complexToRealEuclidean ι m k))
  simpa only [Pi.mul_def, Pi.sub_def, ContinuousLinearMap.coe_comp,
    Function.comp_def, ContinuousLinearEquiv.coe_coe, EuclideanSpace.coe_proj,
    complexToRealEuclidean_apply] using
    (h a).integrable_mul (h b)

private theorem integral_real_centered_product (m : ι → ℂ) {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) (a b : ι ⊕ ι) :
    ∫ z, (Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im) a -
        Sum.elim (fun i ↦ (m i).re) (fun i ↦ (m i).im) a) *
        (Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im) b -
        Sum.elim (fun i ↦ (m i).re) (fun i ↦ (m i).im) b)
        ∂properComplexGaussianMeasure m C = complexGaussianRealCovariance C a b := by
  have hmean (k : ι ⊕ ι) :
      ∫ x, x k ∂multivariateGaussian (complexToRealEuclidean ι m)
        (complexGaussianRealCovariance C) = complexToRealEuclidean ι m k := by
    simpa using (EuclideanSpace.proj k).integral_comp_id_comm
      (μ := multivariateGaussian (complexToRealEuclidean ι m) (complexGaussianRealCovariance C))
      IsGaussian.integrable_id
  have h := covariance_eval_multivariateGaussian (μ := complexToRealEuclidean ι m)
    ((posSemidef_complexGaussianRealCovariance_iff C).2 hC) a b
  simp only [covariance, hmean] at h
  rw [← map_complexToRealEuclidean_properComplexGaussianMeasure m C,
    integral_map (by fun_prop) (by fun_prop)] at h
  simpa only [complexToRealEuclidean_apply] using h

/-- The complex covariance of a proper complex Gaussian is its covariance parameter. -/
theorem integral_mul_conj_sub_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i j : ι) :
    ∫ z, (z i - m i) * star (z j - m j) ∂properComplexGaussianMeasure m C = C i j := by
  have hint := integrable_mul_conj_sub_properComplexGaussianMeasure m C i j
  have hprod := integrable_real_centered_product m C
  have hval := integral_real_centered_product m hC
  have hrr := hval (Sum.inl i) (Sum.inl j)
  have hii := hval (Sum.inr i) (Sum.inr j)
  have hri := hval (Sum.inl i) (Sum.inr j)
  have hir := hval (Sum.inr i) (Sum.inl j)
  have hrr_int := hprod (Sum.inl i) (Sum.inl j)
  have hii_int := hprod (Sum.inr i) (Sum.inr j)
  have hri_int := hprod (Sum.inl i) (Sum.inr j)
  have hir_int := hprod (Sum.inr i) (Sum.inl j)
  simp only [Sum.elim_inl, Sum.elim_inr] at hrr hii hri hir hrr_int hii_int hri_int hir_int
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hint, RCLike.re_eq_complex_re]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
    rw [integral_add hrr_int hii_int, hrr, hii]
    simp
  · rw [← RCLike.im_eq_complex_im, ← integral_im hint, RCLike.im_eq_complex_im]
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, mul_neg]
    rw [integral_add]
    · rw [integral_neg, hri, hir]
      simp
      ring
    · simpa only [Pi.neg_def] using hri_int.neg
    · exact hir_int

/-- The complex pseudocovariance of a proper complex Gaussian vanishes. -/
theorem integral_mul_sub_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i j : ι) :
    ∫ z, (z i - m i) * (z j - m j) ∂properComplexGaussianMeasure m C = 0 := by
  have hint := integrable_mul_sub_properComplexGaussianMeasure m C i j
  have hprod := integrable_real_centered_product m C
  have hval := integral_real_centered_product m hC
  have hrr := hval (Sum.inl i) (Sum.inl j)
  have hii := hval (Sum.inr i) (Sum.inr j)
  have hri := hval (Sum.inl i) (Sum.inr j)
  have hir := hval (Sum.inr i) (Sum.inl j)
  have hrr_int := hprod (Sum.inl i) (Sum.inl j)
  have hii_int := hprod (Sum.inr i) (Sum.inr j)
  have hri_int := hprod (Sum.inl i) (Sum.inr j)
  have hir_int := hprod (Sum.inr i) (Sum.inl j)
  simp only [Sum.elim_inl, Sum.elim_inr] at hrr hii hri hir hrr_int hii_int hri_int hir_int
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hint, RCLike.re_eq_complex_re]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.zero_re]
    rw [integral_sub hrr_int hii_int, hrr, hii]
    simp
  · rw [← RCLike.im_eq_complex_im, ← integral_im hint, RCLike.im_eq_complex_im]
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.zero_im]
    rw [integral_add hri_int hir_int, hri, hir]
    simp [neg_div]

end TauCeti.Probability
