/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MatrixNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix

import TauCeti.LinearAlgebra.Matrix.Vec

/-!
# Densities of matrix normal laws

For positive-definite row and column covariances `U` and `V`, the matrix normal law has density
`(2π)^(-rc/2) det(U)^(-c/2) det(V)^(-r/2)` times
`exp (-trace (V⁻¹ * (X-M)ᵀ * U⁻¹ * (X-M)) / 2)` relative to product Lebesgue measure on entries.
The real and extended nonnegative densities are chosen to be zero outside this parameter range;
no density identity is asserted there, since the law can be singular or a point mass.

Vectorization preserves volume and turns the trace into the quadratic form of the inverse
Kronecker covariance. This transfers `TauCeti.Probability.multivariateGaussian_eq_withDensity`
to matrices and supplies the `HasPDF`, `pdf`, and Radon–Nikodym interfaces. Empty row or column
types are included: their product volume and their normal law are the unique-point probability
measure, with density one at positive-definite parameters.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped Kronecker Matrix ENNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

open Classical in
/-- The real density of a matrix normal law relative to product Lebesgue measure on entries.
It is chosen to be zero unless both covariance parameters are positive definite. -/
def matrixNormalPDFReal (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ)
    (X : Matrix ι κ ℝ) : ℝ :=
  if U.PosDef ∧ V.PosDef then
    (2 * π) ^ (-((Fintype.card ι : ℝ) * Fintype.card κ) / 2) *
      U.det ^ (-(Fintype.card κ : ℝ) / 2) * V.det ^ (-(Fintype.card ι : ℝ) / 2) *
        exp (-(V⁻¹ * (X - M)ᵀ * U⁻¹ * (X - M)).trace / 2)
  else 0

/-- The extended nonnegative density of a matrix normal law. -/
def matrixNormalPDF (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ)
    (X : Matrix ι κ ℝ) : ℝ≥0∞ := ENNReal.ofReal (matrixNormalPDFReal M U V X)

variable {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}

/-- The trace formula for the matrix normal density at positive-definite covariances. -/
theorem matrixNormalPDFReal_of_posDef (M X : Matrix ι κ ℝ) (hU : U.PosDef) (hV : V.PosDef) :
    matrixNormalPDFReal M U V X =
      (2 * π) ^ (-((Fintype.card ι : ℝ) * Fintype.card κ) / 2) *
        U.det ^ (-(Fintype.card κ : ℝ) / 2) * V.det ^ (-(Fintype.card ι : ℝ) / 2) *
          exp (-(V⁻¹ * (X - M)ᵀ * U⁻¹ * (X - M)).trace / 2) :=
  ite_eq_left ⟨hU, hV⟩

/-- The chosen density vanishes outside the positive-definite parameter range. -/
@[simp]
theorem matrixNormalPDFReal_of_not_posDef (M X : Matrix ι κ ℝ)
    (h : ¬(U.PosDef ∧ V.PosDef)) : matrixNormalPDFReal M U V X = 0 := ite_eq_right h

/-- The extended density is the `ENNReal.ofReal` lift of the real density. -/
theorem matrixNormalPDF_eq_ofReal (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ) :
    matrixNormalPDF M U V = fun X => ENNReal.ofReal (matrixNormalPDFReal M U V X) := (rfl)

/-- The chosen extended density vanishes outside the positive-definite parameter range. -/
@[simp]
theorem matrixNormalPDF_of_not_posDef (M X : Matrix ι κ ℝ) (h : ¬(U.PosDef ∧ V.PosDef)) :
    matrixNormalPDF M U V X = 0 := by
  simp only [matrixNormalPDF_eq_ofReal, matrixNormalPDFReal_of_not_posDef M X h,
    ENNReal.ofReal_zero]

/-- The real matrix normal density is nonnegative at every parameter. -/
theorem matrixNormalPDFReal_nonneg (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ)
    (X : Matrix ι κ ℝ) : 0 ≤ matrixNormalPDFReal M U V X := by
  by_cases h : U.PosDef ∧ V.PosDef
  · rw [matrixNormalPDFReal_of_posDef M X h.1 h.2]
    have hdetU := h.1.det_pos
    have hdetV := h.2.det_pos
    positivity
  · rw [matrixNormalPDFReal_of_not_posDef M X h]

/-- At positive-definite covariances the real matrix normal density is everywhere positive. -/
theorem matrixNormalPDFReal_pos (M X : Matrix ι κ ℝ) (hU : U.PosDef) (hV : V.PosDef) :
    0 < matrixNormalPDFReal M U V X := by
  rw [matrixNormalPDFReal_of_posDef M X hU hV]
  have hdetU := hU.det_pos
  have hdetV := hV.det_pos
  positivity

/-- Taking `toReal` recovers the real matrix normal density. -/
@[simp]
theorem toReal_matrixNormalPDF (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ)
    (X : Matrix ι κ ℝ) : (matrixNormalPDF M U V X).toReal = matrixNormalPDFReal M U V X := by
  rw [matrixNormalPDF_eq_ofReal, ENNReal.toReal_ofReal (matrixNormalPDFReal_nonneg M U V X)]

/-- The matrix normal density is finite. -/
@[simp]
theorem matrixNormalPDF_ne_top (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ)
    (X : Matrix ι κ ℝ) : matrixNormalPDF M U V X ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The matrix normal density agrees with the Gaussian density in vectorized coordinates. -/
theorem matrixNormalPDFReal_eq_multivariateGaussianPDFReal (M X : Matrix ι κ ℝ)
    (hU : U.PosDef) (hV : V.PosDef) :
    matrixNormalPDFReal M U V X =
      multivariateGaussianPDFReal (matrixVecMeasurableEquiv 2 M) (V ⊗ₖ U)
        (matrixVecMeasurableEquiv 2 X) := by
  have hquad :
      ⟪matrixVecMeasurableEquiv 2 X - matrixVecMeasurableEquiv 2 M,
        (V ⊗ₖ U)⁻¹.toEuclideanLin
          (matrixVecMeasurableEquiv 2 X - matrixVecMeasurableEquiv 2 M)⟫ =
        (V⁻¹ * (X - M)ᵀ * U⁻¹ * (X - M)).trace := by
    rw [Matrix.inv_kronecker, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [matrixVecMeasurableEquiv_apply, Matrix.toLpLin_apply, WithLp.ofLp_sub,
      WithLp.ofLp_toLp, star_trivial, ← Matrix.vec_sub]
    rw [dotProduct_comm,
      hV.isHermitian.isSymm.inv.vec_dotProduct_kronecker_mulVec_vec,
      Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [matrixNormalPDFReal_of_posDef M X hU hV]
  simp only [multivariateGaussianPDFReal_def, hquad, Matrix.det_kronecker]
  rw [Real.mul_rpow (pow_nonneg hV.det_pos.le _) (pow_nonneg hU.det_pos.le _),
    ← Real.rpow_natCast_mul hV.det_pos.le, ← Real.rpow_natCast_mul hU.det_pos.le]
  simp only [Fintype.card_prod, Nat.cast_mul]
  congr 1
  ring_nf

/-- The real matrix normal density is measurable in the sampled matrix. -/
@[fun_prop]
theorem measurable_matrixNormalPDFReal (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ)
    (V : Matrix κ κ ℝ) : Measurable (matrixNormalPDFReal M U V) := by
  by_cases h : U.PosDef ∧ V.PosDef
  · have heq : matrixNormalPDFReal M U V =
        multivariateGaussianPDFReal (matrixVecMeasurableEquiv 2 M) (V ⊗ₖ U) ∘
          matrixVecMeasurableEquiv 2 :=
      funext fun X => matrixNormalPDFReal_eq_multivariateGaussianPDFReal M X h.1 h.2
    rw [heq]
    exact (measurable_multivariateGaussianPDFReal _ _).comp (MeasurableEquiv.measurable _)
  · have heq : matrixNormalPDFReal M U V = fun _ => 0 :=
      funext fun X => matrixNormalPDFReal_of_not_posDef M X h
    rw [heq]
    exact measurable_const

/-- The extended nonnegative matrix normal density is measurable. -/
@[fun_prop]
theorem measurable_matrixNormalPDF (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ)
    (V : Matrix κ κ ℝ) : Measurable (matrixNormalPDF M U V) :=
  (measurable_matrixNormalPDFReal M U V).ennreal_ofReal

/-- A matrix normal law with positive-definite row and column covariances has the trace-form
density relative to product Lebesgue measure on its entries. -/
theorem matrixNormalMeasure_eq_withDensity (M : Matrix ι κ ℝ) (hU : U.PosDef) (hV : V.PosDef) :
    matrixNormalMeasure M U V = volume.withDensity (matrixNormalPDF M U V) := by
  rw [matrixNormalMeasure_of_posSemidef M hU.posSemidef hV.posSemidef,
    multivariateGaussian_eq_withDensity (hV.kronecker hU),
    MeasurableEquiv.map_withDensity,
    (volume_preserving_matrixVecMeasurableEquiv.symm _).map_eq]
  apply withDensity_congr_ae
  exact ae_of_all _ fun X => by
    simp only [MeasurableEquiv.symm_symm, matrixNormalPDF_eq_ofReal, multivariateGaussianPDF_def]
    simpa only [matrixVecMeasurableEquiv_apply] using
      congrArg ENNReal.ofReal (matrixNormalPDFReal_eq_multivariateGaussianPDFReal M X hU hV).symm

/-- The nonnegative matrix normal density integrates to one at positive-definite covariances. -/
theorem lintegral_matrixNormalPDF_eq_one (M : Matrix ι κ ℝ) (hU : U.PosDef) (hV : V.PosDef) :
    ∫⁻ X, matrixNormalPDF M U V X = 1 := by
  have h : matrixNormalMeasure M U V Set.univ = 1 := measure_univ
  rwa [matrixNormalMeasure_eq_withDensity M hU hV, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- The real matrix normal density integrates to one at positive-definite covariances. -/
theorem integral_matrixNormalPDFReal_eq_one (M : Matrix ι κ ℝ) (hU : U.PosDef) (hV : V.PosDef) :
    ∫ X, matrixNormalPDFReal M U V X = 1 := by
  simp_rw [← toReal_matrixNormalPDF]
  rw [integral_toReal (measurable_matrixNormalPDF M U V).aemeasurable
      (ae_of_all _ fun X => (matrixNormalPDF_ne_top M U V X).lt_top),
    lintegral_matrixNormalPDF_eq_one M hU hV, ENNReal.toReal_one]

/-- The chosen real matrix normal density is integrable for every covariance parameter. -/
theorem integrable_matrixNormalPDFReal (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ)
    (V : Matrix κ κ ℝ) : Integrable (matrixNormalPDFReal M U V) := by
  by_cases h : U.PosDef ∧ V.PosDef
  · apply Integrable.of_integral_ne_zero
    rw [integral_matrixNormalPDFReal_eq_one M h.1 h.2]
    exact one_ne_zero
  · have heq : matrixNormalPDFReal M U V = 0 :=
      funext fun X => matrixNormalPDFReal_of_not_posDef M X h
    rw [heq]
    exact integrable_zero _ _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Matrix ι κ ℝ}
  {M : Matrix ι κ ℝ}

/-- A random matrix with a nondegenerate matrix normal law has a density. -/
theorem hasPDF_of_hasLaw_matrixNormalMeasure (hU : U.PosDef) (hV : V.PosDef)
    (hX : HasLaw X (matrixNormalMeasure M U V) P) : HasPDF X P :=
  Probability.hasPDF_of_hasLaw_withDensity (measurable_matrixNormalPDF M U V).aemeasurable
    (by rwa [← matrixNormalMeasure_eq_withDensity M hU hV])

/-- The density of a random matrix with a nondegenerate matrix normal law. -/
theorem pdf_eq_matrixNormalPDF_of_hasLaw_matrixNormalMeasure (hU : U.PosDef) (hV : V.PosDef)
    (hX : HasLaw X (matrixNormalMeasure M U V) P) : pdf X P =ᵐ[volume] matrixNormalPDF M U V :=
  Probability.pdf_eq_of_hasLaw_withDensity (measurable_matrixNormalPDF M U V).aemeasurable
    (by rwa [← matrixNormalMeasure_eq_withDensity M hU hV])

/-- The Radon–Nikodym derivative of a nondegenerate matrix normal law. -/
theorem rnDeriv_matrixNormalMeasure (M : Matrix ι κ ℝ) (hU : U.PosDef) (hV : V.PosDef) :
    (matrixNormalMeasure M U V).rnDeriv volume =ᵐ[volume] matrixNormalPDF M U V := by
  rw [matrixNormalMeasure_eq_withDensity M hU hV]
  exact Measure.rnDeriv_withDensity _ (measurable_matrixNormalPDF M U V)

end TauCeti.Probability
