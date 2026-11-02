/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Densities of proper complex Gaussian laws

For Hermitian positive-definite covariance `C`, the proper complex Gaussian law has density
`exp (-Re ((z-m)ᴴ C⁻¹ (z-m))) / (π^d * Re (det C))` relative to real product volume
on `ι → ℂ`. The determinant factor is positive. The chosen densities are zero at other
covariance parameters; the density identity is asserted only in the positive-definite case.
Empty coordinate types are included, with density one and the unique-point probability law.

The real-coordinate equivalence preserves volume. Its covariance is half the realification
of `C`, whose determinant is the squared modulus of the complex determinant. These facts
transfer `TauCeti.Probability.multivariateGaussian_eq_withDensity` to complex coordinates,
with the normalization `π^d` rather than `(2π)^d`.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ComplexOrder RealInnerProductSpace Matrix ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The real density of a proper complex Gaussian relative to real product volume.
It is chosen to be zero outside the positive-definite covariance range. -/
def properComplexGaussianPDFReal (m : ι → ℂ) (C : Matrix ι ι ℂ) (z : ι → ℂ) : ℝ :=
  if C.PosDef then
    exp (-(star (z - m) ⬝ᵥ C⁻¹ *ᵥ (z - m)).re) / (π ^ Fintype.card ι * C.det.re)
  else 0

/-- The extended nonnegative density of a proper complex Gaussian. -/
def properComplexGaussianPDF (m : ι → ℂ) (C : Matrix ι ι ℂ) (z : ι → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (properComplexGaussianPDFReal m C z)

variable {C : Matrix ι ι ℂ}

/-- The Hermitian quadratic-form formula for the density at positive-definite covariance. -/
theorem properComplexGaussianPDFReal_of_posDef (m z : ι → ℂ) (hC : C.PosDef) :
    properComplexGaussianPDFReal m C z =
      exp (-(star (z - m) ⬝ᵥ C⁻¹ *ᵥ (z - m)).re) / (π ^ Fintype.card ι * C.det.re) :=
  ite_eq_left hC

/-- The chosen real density is zero outside the positive-definite covariance range. -/
@[simp]
theorem properComplexGaussianPDFReal_of_not_posDef (m z : ι → ℂ) (hC : ¬ C.PosDef) :
    properComplexGaussianPDFReal m C z = 0 := ite_eq_right hC

/-- The extended density is the `ENNReal.ofReal` lift of the real density. -/
theorem properComplexGaussianPDF_eq_ofReal (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    properComplexGaussianPDF m C = fun z ↦ ENNReal.ofReal (properComplexGaussianPDFReal m C z) :=
  (rfl)

/-- The chosen extended density is zero outside the positive-definite covariance range. -/
@[simp]
theorem properComplexGaussianPDF_of_not_posDef (m z : ι → ℂ) (hC : ¬ C.PosDef) :
    properComplexGaussianPDF m C z = 0 := by
  simp [properComplexGaussianPDF_eq_ofReal, properComplexGaussianPDFReal_of_not_posDef m z hC]

/-- The real density is everywhere positive at positive-definite covariance. -/
theorem properComplexGaussianPDFReal_pos (m z : ι → ℂ) (hC : C.PosDef) :
    0 < properComplexGaussianPDFReal m C z := by
  rw [properComplexGaussianPDFReal_of_posDef m z hC]
  have hd := (Complex.pos_iff.mp hC.det_pos).1
  positivity

/-- The real density is nonnegative at every parameter. -/
theorem properComplexGaussianPDFReal_nonneg (m : ι → ℂ) (C : Matrix ι ι ℂ) (z : ι → ℂ) :
    0 ≤ properComplexGaussianPDFReal m C z := by
  by_cases hC : C.PosDef
  · exact (properComplexGaussianPDFReal_pos m z hC).le
  · rw [properComplexGaussianPDFReal_of_not_posDef m z hC]

/-- The extended density is everywhere positive at positive-definite covariance. -/
theorem properComplexGaussianPDF_pos (m z : ι → ℂ) (hC : C.PosDef) :
    0 < properComplexGaussianPDF m C z :=
  ENNReal.ofReal_pos.mpr (properComplexGaussianPDFReal_pos m z hC)

/-- Taking `toReal` recovers the real density. -/
@[simp]
theorem toReal_properComplexGaussianPDF (m : ι → ℂ) (C : Matrix ι ι ℂ) (z : ι → ℂ) :
    (properComplexGaussianPDF m C z).toReal = properComplexGaussianPDFReal m C z := by
  rw [properComplexGaussianPDF_eq_ofReal,
    ENNReal.toReal_ofReal (properComplexGaussianPDFReal_nonneg m C z)]

/-- The extended density is finite at every parameter. -/
@[simp]
theorem properComplexGaussianPDF_ne_top (m : ι → ℂ) (C : Matrix ι ι ℂ) (z : ι → ℂ) :
    properComplexGaussianPDF m C z ≠ ⊤ := ENNReal.ofReal_ne_top

private theorem normalizer_complexGaussianRealCovariance (hC : C.PosDef) :
    (2 * π) ^ (-(Fintype.card (ι ⊕ ι) : ℝ) / 2) *
      (complexGaussianRealCovariance C).det ^ (-(1 : ℝ) / 2) =
        (π ^ Fintype.card ι * C.det.re)⁻¹ := by
  have hd : 0 < C.det.re := (Complex.pos_iff.mp hC.det_pos).1
  have him : C.det.im = 0 := (Complex.pos_iff.mp hC.det_pos).2.symm
  rw [complexGaussianRealCovariance_def, Matrix.det_smul, Matrix.det_realify]
  simp only [Fintype.card_sum, Nat.cast_add, Complex.normSq_apply, him, mul_zero, add_zero]
  rw [← pow_two]
  rw [Real.mul_rpow (by positivity) (sq_nonneg _),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), ← Real.rpow_natCast_mul hd.le]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  have he : ((Fintype.card ι : ℝ) + Fintype.card ι) * (-(1 : ℝ) / 2) =
      -(Fintype.card ι : ℝ) := by ring
  rw [he]
  norm_num
  simp only [Real.rpow_neg_one, mul_pow, one_div, inv_pow, mul_inv_rev]
  field_simp

private theorem inner_inv_complexGaussianRealCovariance (hC : C.PosDef) (z : ι → ℂ) :
    ⟪complexToRealEuclidean ι z,
      (complexGaussianRealCovariance C)⁻¹.toEuclideanLin (complexToRealEuclidean ι z)⟫ =
        2 * (star z ⬝ᵥ C⁻¹ *ᵥ z).re := by
  have hinv : (complexGaussianRealCovariance C)⁻¹ = (2 : ℝ) • (C⁻¹).realify := by
    apply Matrix.inv_eq_left_inv
    rw [complexGaussianRealCovariance_def, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← Matrix.realify_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hC.det_pos.ne')]
    norm_num
  have hz : ((complexToRealEuclidean ι) z).ofLp =
      Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im) := by
    ext j
    simp
  rw [hinv, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, star_trivial, hz]
  rw [dotProduct_comm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact congrArg (fun x : ℝ ↦ 2 * x) (Matrix.dotProduct_realify_mulVec C⁻¹ z)

/-- The complex density agrees with the real Gaussian density in split coordinates. -/
theorem properComplexGaussianPDFReal_eq_multivariateGaussianPDFReal (m z : ι → ℂ)
    (hC : C.PosDef) :
    properComplexGaussianPDFReal m C z =
      multivariateGaussianPDFReal (complexToRealEuclidean ι m) (complexGaussianRealCovariance C)
        (complexToRealEuclidean ι z) := by
  rw [properComplexGaussianPDFReal_of_posDef m z hC]
  simp only [multivariateGaussianPDFReal_def, ← map_sub]
  rw [normalizer_complexGaussianRealCovariance hC,
    inner_inv_complexGaussianRealCovariance hC]
  rw [div_eq_mul_inv, mul_comm]
  congr 2
  ring

/-- The real density is measurable in the sampled complex vector. -/
@[fun_prop]
theorem measurable_properComplexGaussianPDFReal (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    Measurable (properComplexGaussianPDFReal m C) := by
  by_cases hC : C.PosDef
  · have heq : properComplexGaussianPDFReal m C =
        multivariateGaussianPDFReal (complexToRealEuclidean ι m) (complexGaussianRealCovariance C) ∘
          complexToRealEuclidean ι :=
      funext fun z ↦ properComplexGaussianPDFReal_eq_multivariateGaussianPDFReal m z hC
    rw [heq]
    exact (measurable_multivariateGaussianPDFReal _ _).comp (by fun_prop)
  · have heq : properComplexGaussianPDFReal m C = fun _ ↦ 0 :=
      funext fun z ↦ properComplexGaussianPDFReal_of_not_posDef m z hC
    rw [heq]
    exact measurable_const

/-- The extended density is measurable in the sampled complex vector. -/
@[fun_prop]
theorem measurable_properComplexGaussianPDF (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    Measurable (properComplexGaussianPDF m C) :=
  (measurable_properComplexGaussianPDFReal m C).ennreal_ofReal

/-- A proper complex Gaussian at positive-definite covariance has the Hermitian
quadratic-form density relative to real product Lebesgue measure. -/
theorem properComplexGaussianMeasure_eq_withDensity (m : ι → ℂ) (hC : C.PosDef) :
    properComplexGaussianMeasure m C = volume.withDensity (properComplexGaussianPDF m C) := by
  have hS : (complexGaussianRealCovariance C).PosDef := by
    have hpos := (posSemidef_complexGaussianRealCovariance_iff C).2 hC.posSemidef
    apply hpos.posDef_iff_det_ne_zero.mpr
    rw [complexGaussianRealCovariance_def, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Matrix.isUnit_det_realify (isUnit_iff_ne_zero.mpr hC.det_pos.ne')).ne_zero
  rw [properComplexGaussianMeasure_def, multivariateGaussian_eq_withDensity hS]
  let e := (complexToRealEuclidean ι).toHomeomorph.toMeasurableEquiv
  have hmap := MeasurableEquiv.map_withDensity e.symm volume
    (multivariateGaussianPDF (complexToRealEuclidean ι m) (complexGaussianRealCovariance C))
  rw [(volume_preserving_complexToRealEuclidean.symm e).map_eq] at hmap
  have he : (e.symm : EuclideanSpace ℝ (ι ⊕ ι) → ι → ℂ) =
      (complexToRealEuclidean ι).symm := by
    simp only [e, Homeomorph.toMeasurableEquiv_symm_coe,
      ContinuousLinearEquiv.coe_symm_toHomeomorph]
  rw [he] at hmap
  rw [hmap]
  apply withDensity_congr_ae
  exact ae_of_all _ fun z ↦ by
    simp only [properComplexGaussianPDF_eq_ofReal, multivariateGaussianPDF_def]
    exact congrArg ENNReal.ofReal
      (properComplexGaussianPDFReal_eq_multivariateGaussianPDFReal m z hC).symm

/-- The extended density integrates to one at positive-definite covariance. -/
theorem lintegral_properComplexGaussianPDF_eq_one (m : ι → ℂ) (hC : C.PosDef) :
    ∫⁻ z, properComplexGaussianPDF m C z = 1 := by
  have h : properComplexGaussianMeasure m C Set.univ = 1 := measure_univ
  rwa [properComplexGaussianMeasure_eq_withDensity m hC,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h

/-- The real density integrates to one at positive-definite covariance. -/
theorem integral_properComplexGaussianPDFReal_eq_one (m : ι → ℂ) (hC : C.PosDef) :
    ∫ z, properComplexGaussianPDFReal m C z = 1 := by
  simp_rw [← toReal_properComplexGaussianPDF]
  rw [integral_toReal (measurable_properComplexGaussianPDF m C).aemeasurable
      (ae_of_all _ fun z ↦ (properComplexGaussianPDF_ne_top m C z).lt_top),
    lintegral_properComplexGaussianPDF_eq_one m hC, ENNReal.toReal_one]

/-- The chosen real density is integrable at every covariance parameter. -/
theorem integrable_properComplexGaussianPDFReal (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    Integrable (properComplexGaussianPDFReal m C) := by
  by_cases hC : C.PosDef
  · apply Integrable.of_integral_ne_zero
    rw [integral_properComplexGaussianPDFReal_eq_one m hC]
    exact one_ne_zero
  · have heq : properComplexGaussianPDFReal m C = 0 :=
      funext fun z ↦ properComplexGaussianPDFReal_of_not_posDef m z hC
    rw [heq]
    exact integrable_zero _ _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ι → ℂ} {m : ι → ℂ}

/-- A random vector with a nondegenerate proper complex Gaussian law has a density. -/
theorem hasPDF_of_hasLaw_properComplexGaussianMeasure (hC : C.PosDef)
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) : HasPDF Z P :=
  Probability.hasPDF_of_hasLaw_withDensity (measurable_properComplexGaussianPDF m C).aemeasurable
    (by rwa [← properComplexGaussianMeasure_eq_withDensity m hC])

/-- The density of a random vector with a nondegenerate proper complex Gaussian law. -/
theorem pdf_eq_properComplexGaussianPDF_of_hasLaw_properComplexGaussianMeasure (hC : C.PosDef)
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) :
    pdf Z P =ᵐ[volume] properComplexGaussianPDF m C :=
  Probability.pdf_eq_of_hasLaw_withDensity (measurable_properComplexGaussianPDF m C).aemeasurable
    (by rwa [← properComplexGaussianMeasure_eq_withDensity m hC])

/-- The Radon–Nikodym derivative of a nondegenerate proper complex Gaussian law. -/
theorem rnDeriv_properComplexGaussianMeasure (m : ι → ℂ) (hC : C.PosDef) :
    (properComplexGaussianMeasure m C).rnDeriv volume =ᵐ[volume] properComplexGaussianPDF m C := by
  rw [properComplexGaussianMeasure_eq_withDensity m hC]
  exact Measure.rnDeriv_withDensity _ (measurable_properComplexGaussianPDF m C)

end TauCeti.Probability
