/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Analysis.Matrix.Realify
public import TauCeti.Probability.Distributions.Gaussian.Multivariate

/-!
# Proper complex Gaussian laws

A proper complex Gaussian vector with mean `m` and Hermitian positive semidefinite
covariance `C` is a real Gaussian in split coordinates with covariance
`(1 / 2) • !![Re C, -Im C; Im C, Re C]`. The factor one half ensures that the complex
covariance is `C`, while the complex pseudocovariance vanishes.

This file constructs the law on the product Borel space `ι → ℂ`, identifies its real
coordinate law, and proves probability, the mean, parameter measurability, and the
zero-covariance and invalid-covariance Dirac cases. Singular covariance matrices and
empty coordinate types are included.

The construction uses `Matrix.realify`, `complexToRealEuclidean`, and Mathlib's
`multivariateGaussian`.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder

namespace TauCeti.Probability

variable {ι : Type*}

/-- The real covariance of a proper complex Gaussian with complex covariance `C`, in
real-then-imaginary coordinate order. -/
def complexGaussianRealCovariance (C : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  (2⁻¹ : ℝ) • C.realify

/-- The real covariance is one half of the realification of the complex covariance. -/
theorem complexGaussianRealCovariance_def (C : Matrix ι ι ℂ) :
    complexGaussianRealCovariance C = (2⁻¹ : ℝ) • C.realify := (rfl)

@[simp]
theorem complexGaussianRealCovariance_inl_inl (C : Matrix ι ι ℂ) (i j : ι) :
    complexGaussianRealCovariance C (Sum.inl i) (Sum.inl j) = (C i j).re / 2 := by
  simp [complexGaussianRealCovariance, div_eq_mul_inv, mul_comm]

@[simp]
theorem complexGaussianRealCovariance_inl_inr (C : Matrix ι ι ℂ) (i j : ι) :
    complexGaussianRealCovariance C (Sum.inl i) (Sum.inr j) = -(C i j).im / 2 := by
  simp [complexGaussianRealCovariance, div_eq_mul_inv, mul_comm]

@[simp]
theorem complexGaussianRealCovariance_inr_inl (C : Matrix ι ι ℂ) (i j : ι) :
    complexGaussianRealCovariance C (Sum.inr i) (Sum.inl j) = (C i j).im / 2 := by
  simp [complexGaussianRealCovariance, div_eq_mul_inv, mul_comm]

@[simp]
theorem complexGaussianRealCovariance_inr_inr (C : Matrix ι ι ℂ) (i j : ι) :
    complexGaussianRealCovariance C (Sum.inr i) (Sum.inr j) = (C i j).re / 2 := by
  simp [complexGaussianRealCovariance, div_eq_mul_inv, mul_comm]

/-- Zero complex covariance has zero real covariance. -/
@[simp]
theorem complexGaussianRealCovariance_zero :
    complexGaussianRealCovariance (0 : Matrix ι ι ℂ) = 0 := by
  simp [complexGaussianRealCovariance]

/-- Real and complex covariance validity agree on finite coordinate types. -/
@[simp]
theorem posSemidef_complexGaussianRealCovariance_iff [Finite ι] (C : Matrix ι ι ℂ) :
    (complexGaussianRealCovariance C).PosSemidef ↔ C.PosSemidef := by
  constructor
  · intro h
    apply Matrix.posSemidef_realify_iff.mp
    simpa [complexGaussianRealCovariance, smul_smul] using h.smul (by norm_num : (0 : ℝ) ≤ 2)
  · intro h
    exact (Matrix.posSemidef_realify_iff.mpr h).smul (by norm_num : (0 : ℝ) ≤ 2⁻¹)

/-- The real covariance depends continuously on the complex matrix entries. -/
@[fun_prop]
theorem continuous_complexGaussianRealCovariance :
    Continuous (complexGaussianRealCovariance (ι := ι)) := by
  apply continuous_matrix
  intro i j
  cases i <;> cases j <;> simp only [complexGaussianRealCovariance_inl_inl,
    complexGaussianRealCovariance_inl_inr, complexGaussianRealCovariance_inr_inl,
    complexGaussianRealCovariance_inr_inr] <;> fun_prop

variable [Fintype ι] [DecidableEq ι]

/-- The proper complex Gaussian law with mean `m` and covariance `C`. For a covariance
that is not Hermitian positive semidefinite, it is the Dirac law at `m`. -/
def properComplexGaussianMeasure (m : ι → ℂ) (C : Matrix ι ι ℂ) : Measure (ι → ℂ) :=
  (multivariateGaussian (complexToRealEuclidean ι m) (complexGaussianRealCovariance C)).map
    (complexToRealEuclidean ι).symm

/-- The proper complex Gaussian law is the real Gaussian read in complex coordinates. -/
theorem properComplexGaussianMeasure_def (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    properComplexGaussianMeasure m C =
      (multivariateGaussian (complexToRealEuclidean ι m) (complexGaussianRealCovariance C)).map
        (complexToRealEuclidean ι).symm := (rfl)

instance isProbabilityMeasure_properComplexGaussianMeasure (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    IsProbabilityMeasure (properComplexGaussianMeasure m C) := by
  rw [properComplexGaussianMeasure_def]
  infer_instance

/-- A proper complex Gaussian is Gaussian when its carrier is regarded as a real vector
space. This includes its invalid-covariance fallback. -/
instance isGaussian_properComplexGaussianMeasure (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    IsGaussian (properComplexGaussianMeasure m C) := by
  rw [properComplexGaussianMeasure_def]
  infer_instance

/-- Splitting real and imaginary coordinates recovers the defining real Gaussian law. -/
@[simp]
theorem map_complexToRealEuclidean_properComplexGaussianMeasure (m : ι → ℂ)
    (C : Matrix ι ι ℂ) :
    (properComplexGaussianMeasure m C).map (complexToRealEuclidean ι) =
      multivariateGaussian (complexToRealEuclidean ι m) (complexGaussianRealCovariance C) := by
  rw [properComplexGaussianMeasure_def,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- An invalid complex covariance gives the point mass at the mean. -/
theorem properComplexGaussianMeasure_of_not_posSemidef (m : ι → ℂ) {C : Matrix ι ι ℂ}
    (hC : ¬ C.PosSemidef) : properComplexGaussianMeasure m C = Measure.dirac m := by
  rw [properComplexGaussianMeasure_def, multivariateGaussian_of_not_posSemidef _
    (by simpa using hC), Measure.map_dirac' (by fun_prop),
    ContinuousLinearEquiv.symm_apply_apply]

/-- Zero covariance gives the point mass at the mean. -/
@[simp]
theorem properComplexGaussianMeasure_zero (m : ι → ℂ) :
    properComplexGaussianMeasure m 0 = Measure.dirac m := by
  simp [properComplexGaussianMeasure_def]

/-- The Bochner mean is the mean parameter, at every covariance. -/
@[simp]
theorem integral_id_properComplexGaussianMeasure (m : ι → ℂ) (C : Matrix ι ι ℂ) :
    ∫ z, z ∂properComplexGaussianMeasure m C = m := by
  rw [properComplexGaussianMeasure_def, integral_map (by fun_prop) (by fun_prop),
    (complexToRealEuclidean ι).symm.integral_comp_id_comm, integral_id_multivariateGaussian,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Joint parameter measurability, including the invalid-covariance Dirac branch. -/
@[fun_prop]
theorem measurable_properComplexGaussianMeasure :
    Measurable fun q : (ι → ℂ) × (ι → ι → ℂ) ↦
      properComplexGaussianMeasure q.1 (Matrix.of q.2) := by
  simp only [properComplexGaussianMeasure_def]
  apply (Measure.measurable_map (complexToRealEuclidean ι).symm (by fun_prop)).comp
  exact measurable_multivariateGaussian.comp
    ((complexToRealEuclidean ι).continuous.measurable.comp measurable_fst |>.prodMk
      (continuous_complexGaussianRealCovariance.measurable.comp measurable_snd))

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {Z : Ω → ι → ℂ} {m : ι → ℂ} {C : Matrix ι ι ℂ}

/-- The real and imaginary coordinate blocks of a proper complex Gaussian random vector
have the associated real multivariate Gaussian law. -/
theorem HasLaw.complexToRealEuclidean_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) :
    HasLaw (fun ω ↦ complexToRealEuclidean ι (Z ω))
      (multivariateGaussian (complexToRealEuclidean ι m) (complexGaussianRealCovariance C)) P := by
  rw [← map_complexToRealEuclidean_properComplexGaussianMeasure]
  exact (hasLaw_map (complexToRealEuclidean ι).continuous.measurable.aemeasurable).comp hZ

end ProbabilityTheory
